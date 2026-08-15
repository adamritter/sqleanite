import SQLeanite.CoreChunkPageState
import SQLeanite.CoreDecode

namespace SQLeanite
namespace CorePageCodec

structure NumberedPage where
  pageNumber : Nat
  page : CoreFile.Page

def encodeLeaf (schema : Core.Schema)
    (entries : List (PagedBTree.Entry Core.Row)) : Option CoreFile.Page := do
  let cells ← entries.mapM fun entry => CoreRecord.encodeCell? schema entry.2
  CoreFile.tableLeafPage? cells

private theorem mapM_map_entry_values
    (entries : List (PagedBTree.Entry Core.Row))
    (encode : Core.Row → Option (List UInt8)) :
    (entries.map fun entry => entry.2).mapM encode =
      entries.mapM (fun entry => encode entry.2) := by
  induction entries with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.map_cons, List.mapM_cons, induction]

theorem decodeCanonicalRows_encodeLeaf (schema : Core.Schema)
    (entries : List (PagedBTree.Entry Core.Row)) (page : CoreFile.Page)
    (valid : ∀ entry ∈ entries, entry.2.WellFormed schema)
    (encoded : encodeLeaf schema entries = some page) :
    CoreDecode.decodeCanonicalRows schema 0 page.bytes =
      some (entries.map fun entry => entry.2) := by
  unfold encodeLeaf at encoded
  cases cellsResult : entries.mapM
      (fun entry => CoreRecord.encodeCell? schema entry.2) with
  | none => simp [cellsResult] at encoded
  | some cells =>
      simp only [cellsResult, Option.bind_eq_bind, Option.bind] at encoded
      cases bodyResult : CoreFile.leafBody? 13 0 cells with
      | none => simp [CoreFile.tableLeafPage?, bodyResult] at encoded
      | some body =>
          simp only [CoreFile.tableLeafPage?, bodyResult, Option.bind_eq_bind,
            Option.bind, Option.some.injEq] at encoded
          subst page
          rcases CoreFile.leafBody_table_exact bodyResult with ⟨bodyBytes, fits⟩
          change CoreDecode.decodeCanonicalRows schema 0 body.bytes = _
          rw [bodyBytes]
          refine CoreDecode.decodeCanonicalRows_leafPageBody schema
            (entries.map fun entry => entry.2) cells [] 0 rfl fits ?_ ?_
          · intro row member
            simp only [List.mem_map] at member
            rcases member with ⟨entry, entryMember, rfl⟩
            exact valid entry entryMember
          · rw [mapM_map_entry_values]
            exact cellsResult

def maximumChunkRowid? (node : PersistentPageTree.Node
    CoreChunkPageState.Chunk) : Option Nat :=
  node.erase.toList.getLast?.bind fun entry =>
    entry.2.getLast?.map (fun row => row.rowid.toUnsigned)

theorem maximumChunkRowid?_witness
    {node : PersistentPageTree.Node CoreChunkPageState.Chunk} {key : Nat}
    (found : maximumChunkRowid? node = some key) :
    ∃ row, (CoreChunkPageState.Node.rows node).getLast? = some row ∧
      key = row.rowid.toUnsigned := by
  unfold maximumChunkRowid? at found
  cases entryResult : node.erase.toList.getLast? with
  | none => simp [entryResult] at found
  | some entry =>
      rw [entryResult] at found
      cases rowResult : entry.2.getLast? with
      | none => simp [rowResult] at found
      | some row =>
          simp only [rowResult, Option.bind_eq_bind, Option.bind, Option.map,
            Option.some.injEq] at found
          subst key
          rcases List.getLast?_eq_some_iff.mp entryResult with
            ⟨entries, entriesEqual⟩
          rcases List.getLast?_eq_some_iff.mp rowResult with
            ⟨rows, rowsEqual⟩
          refine ⟨row, ?_, rfl⟩
          unfold CoreChunkPageState.Node.rows
          rw [entriesEqual]
          simp [rowsEqual, List.flatMap_append]

private def findRowid (target : Core.Integer) (rows : List Core.Row) :
    Option Core.Row :=
  rows.find? fun row => row.rowid = target

/-- In a globally ordered row sequence, the greatest rowid of the left side
is an exact routing separator.  This is the logical fact used by both physical
interior-page shapes. -/
private theorem findRowid_append_routed (target boundary : Core.Integer)
    (left right : List Core.Row)
    (ordered : (left ++ right).Pairwise Core.Row.keyLess)
    (lastLeft : left.getLast?.map Core.Row.rowid = some boundary) :
    findRowid target (left ++ right) =
      if target.value ≤ boundary.value then findRowid target left
      else findRowid target right := by
  have existsLast : ∃ last, left.getLast? = some last ∧
      last.rowid = boundary := by
    cases lastResult : left.getLast? with
    | none => simp [lastResult] at lastLeft
    | some last =>
        refine ⟨last, rfl, ?_⟩
        simpa [lastResult] using lastLeft
  rcases existsLast with ⟨last, lastResult, lastBoundary⟩
  subst boundary
  have lastMember : last ∈ left := by
    rcases List.getLast?_eq_some_iff.mp lastResult with ⟨front, equal⟩
    subst left
    simp
  have splitOrdered := List.pairwise_append.mp ordered
  unfold findRowid
  rw [List.find?_append]
  split <;> rename_i routed
  · cases leftResult : left.find? (fun row => row.rowid = target) with
    | some row => simp [leftResult]
    | none =>
        have rightNone : right.find? (fun row => row.rowid = target) = none := by
          apply List.find?_eq_none.mpr
          intro row member matched
          have after := splitOrdered.2.2 last lastMember row member
          have unequal : row.rowid ≠ target := by
            intro equal
            have values := congrArg FileFormat.SignedInteger.value equal
            unfold Core.Row.keyLess at after
            omega
          exact unequal (by simpa only [decide_eq_true_eq] using matched)
        simp [rightNone]
  · have leftNone : left.find? (fun row => row.rowid = target) = none := by
      apply List.find?_eq_none.mpr
      intro row member matched
      have rowBeforeOrEqual : row.rowid.value ≤ last.rowid.value := by
        rcases List.getLast?_eq_some_iff.mp lastResult with ⟨front, equal⟩
        subst left
        rw [List.mem_append] at member
        rcases member with frontMember | lastEqual
        · have pairwise := List.pairwise_append.mp splitOrdered.1
          exact Int.le_of_lt (pairwise.2.2 row frontMember last (by simp))
        · have equal : row = last := List.mem_singleton.mp lastEqual
          subst row
          exact Int.le_refl _
      have unequal : row.rowid ≠ target := by
        intro equal
        have values := congrArg FileFormat.SignedInteger.value equal
        omega
      exact unequal (by simpa only [decide_eq_true_eq] using matched)
    simp [leftNone]

private theorem rowid_le_of_pairwise_last
    {rows : List Core.Row} {last : Core.Row}
    (ordered : rows.Pairwise Core.Row.keyLess)
    (lastResult : rows.getLast? = some last) :
    ∀ row ∈ rows, row.rowid.value ≤ last.rowid.value := by
  induction rows with
  | nil => simp at lastResult
  | cons head tail induction =>
      intro row member
      cases tail with
      | nil =>
          simp at member lastResult
          subst row
          subst head
          exact Int.le_refl _
      | cons next rest =>
          have tailOrdered : (next :: rest).Pairwise Core.Row.keyLess :=
            (List.pairwise_cons.mp ordered).2
          have tailLast : (next :: rest).getLast? = some last := by
            simpa using lastResult
          have lastInTail : last ∈ next :: rest := by
            rcases List.getLast?_eq_some_iff.mp tailLast with ⟨front, equal⟩
            rw [equal]
            simp
          simp only [List.mem_cons] at member
          cases member with
          | inl equal =>
              subst row
              have before := (List.pairwise_cons.mp ordered).1 last lastInTail
              exact Int.le_of_lt before
          | inr tailMember =>
              exact induction tailOrdered tailLast row (by simpa using tailMember)

def encodeChunkLeaf (schema : Core.Schema)
    (entries : List (PagedBTree.Entry CoreChunkPageState.Chunk)) :
    Option CoreFile.Page :=
  encodeLeaf schema (entries.flatMap fun entry =>
    entry.2.map fun row => (row.treeKey, row))

theorem canonicalPointersBeginAtContent_encodeChunkLeaf (schema : Core.Schema)
    (entries : List (PagedBTree.Entry CoreChunkPageState.Chunk))
    (page : CoreFile.Page)
    (encoded : encodeChunkLeaf schema entries = some page) :
    CoreDecode.canonicalPointersBeginAtContent page.bytes = true := by
  unfold encodeChunkLeaf encodeLeaf at encoded
  cases cellsResult :
      (entries.flatMap fun entry =>
        entry.2.map fun row => (row.treeKey, row)).mapM
          (fun entry => CoreRecord.encodeCell? schema entry.2) with
  | none => simp [cellsResult] at encoded
  | some cells =>
      simp only [cellsResult, Option.bind_eq_bind, Option.bind] at encoded
      cases bodyResult : CoreFile.leafBody? 13 0 cells with
      | none => simp [CoreFile.tableLeafPage?, bodyResult] at encoded
      | some body =>
          simp only [CoreFile.tableLeafPage?, bodyResult, Option.bind_eq_bind,
            Option.bind, Option.some.injEq] at encoded
          subst page
          rcases CoreFile.leafBody_table_exact bodyResult with
            ⟨bodyBytes, fits⟩
          change CoreDecode.canonicalPointersBeginAtContent body.bytes = true
          rw [bodyBytes]
          let contentStart := PhysicalCodec.pageSize -
            (PhysicalCodec.cellBytes cells).length
          have countBound : cells.length < 256 ^ 2 := by
            simpa using fits.cellCount_lt
          have contentBound : contentStart < 256 ^ 2 := by
            simpa [contentStart] using PhysicalCodec.contentStart_lt cells
          cases cells with
          | nil =>
              simp [CoreDecode.canonicalPointersBeginAtContent,
                PhysicalCodec.leafPageBody, PhysicalCodec.leafHeader,
                PhysicalCodec.leafPointers, PhysicalCodec.cellOffsetsFrom,
                PhysicalCodec.encodeU16Nat, FileFormat.encodeUnsignedFixed,
                FileFormat.decodeU16]
          | cons cell cells =>
              simp [CoreDecode.canonicalPointersBeginAtContent,
                PhysicalCodec.leafPageBody, PhysicalCodec.leafHeader,
                PhysicalCodec.leafPointers, PhysicalCodec.cellOffsetsFrom,
                PhysicalCodec.encodeU16Nat, FileFormat.encodeUnsignedFixed,
                FileFormat.decodeU16, contentStart]

/- Retained as historical proof text for the superseded inline-only encoder.
The live decoder now prefers the overflow-aware packed-cell path, and the
stronger inverse below covers both inline and overflow payloads.
theorem decodeRowsFrom_encodeChunkLeaf (schema : Core.Schema)
    (entries : List (PagedBTree.Entry CoreChunkPageState.Chunk))
    (page : CoreFile.Page)
    (valid : ∀ entry ∈ entries, ∀ row ∈ entry.2, row.WellFormed schema)
    (encoded : encodeChunkLeaf schema entries = some page)
    (source : CoreDecode.PageSource) :
    CoreDecode.decodeRowsFrom schema source page.bytes =
      some (entries.flatMap fun entry => entry.2) := by
  let rows := entries.flatMap fun entry =>
    entry.2.map fun row => (row.treeKey, row)
  have rowValid : ∀ entry ∈ rows, entry.2.WellFormed schema := by
    intro candidate member
    simp only [rows, List.mem_flatMap, List.mem_map] at member
    rcases member with ⟨entry, entryMember, row, rowMember, equal⟩
    cases equal
    exact valid entry entryMember row rowMember
  have canonical := decodeCanonicalRows_encodeLeaf schema rows page rowValid encoded
  unfold CoreDecode.decodeRowsFrom
  rw [canonicalPointersBeginAtContent_encodeChunkLeaf schema entries page encoded]
  simp only [Bool.true_eq, if_true]
  rw [canonical]
  congr 2
  simp [rows, List.map_flatMap, Function.comp_def]
-/

/-- A page emitted by the chunk-leaf encoder is classified as a leaf by the
recursive decoder.  This is the page-tag half of the raw encoder inverse: an
encoded leaf cannot accidentally be traversed as an interior page. -/
theorem interiorChildren_encodeChunkLeaf (schema : Core.Schema)
    (entries : List (PagedBTree.Entry CoreChunkPageState.Chunk))
    (page : CoreFile.Page)
    (encoded : encodeChunkLeaf schema entries = some page) :
    CoreDecode.interiorChildren? page.bytes = none := by
  unfold encodeChunkLeaf encodeLeaf at encoded
  cases cellsResult :
      (entries.flatMap fun entry =>
        entry.2.map fun row => (row.treeKey, row)).mapM
          (fun entry => CoreRecord.encodeCell? schema entry.2) with
  | none => simp [cellsResult] at encoded
  | some cells =>
      simp only [cellsResult, Option.bind_eq_bind, Option.bind] at encoded
      cases bodyResult : CoreFile.leafBody? 13 0 cells with
      | none => simp [CoreFile.tableLeafPage?, bodyResult] at encoded
      | some body =>
          simp only [CoreFile.tableLeafPage?, bodyResult, Option.bind_eq_bind,
            Option.bind, Option.some.injEq] at encoded
          subst page
          rcases CoreFile.leafBody_table_exact bodyResult with
            ⟨bodyBytes, fits⟩
          change CoreDecode.interiorChildren? body.bytes = none
          rw [bodyBytes]
          unfold CoreDecode.interiorChildren?
          rw [if_pos (by
            simpa using PhysicalCodec.leafPageBody_length 0 cells fits)]
          unfold PhysicalCodec.leafPageBody PhysicalCodec.leafHeader
          rfl

theorem interiorChildren_tableLeafPage {cells : List (List UInt8)}
    {page : CoreFile.Page}
    (built : CoreFile.tableLeafPage? cells = some page) :
    CoreDecode.interiorChildren? page.bytes = none := by
  unfold CoreFile.tableLeafPage? at built
  cases bodyResult : CoreFile.leafBody? 13 0 cells with
  | none => simp [bodyResult] at built
  | some body =>
      simp only [bodyResult, Option.bind_eq_bind, Option.bind,
        Option.some.injEq] at built
      subst page
      rcases CoreFile.leafBody_table_exact bodyResult with ⟨bodyBytes, fits⟩
      change CoreDecode.interiorChildren? body.bytes = none
      rw [bodyBytes]
      unfold CoreDecode.interiorChildren?
      rw [if_pos (by
        simpa using PhysicalCodec.leafPageBody_length 0 cells fits)]
      unfold PhysicalCodec.leafPageBody PhysicalCodec.leafHeader
      rfl

/-- The routing decoder agrees that an encoded chunk leaf is not an interior
page.  Unlike `interiorChildren_encodeChunkLeaf`, this is about the exact
decoder used by cold primary-key lookup. -/
theorem decodeTableInterior_encodeChunkLeaf (schema : Core.Schema)
    (entries : List (PagedBTree.Entry CoreChunkPageState.Chunk))
    (page : CoreFile.Page)
    (encoded : encodeChunkLeaf schema entries = some page) :
    CoreDecode.decodeTableInterior? page.bytes = none := by
  unfold encodeChunkLeaf encodeLeaf at encoded
  cases cellsResult :
      (entries.flatMap fun entry =>
        entry.2.map fun row => (row.treeKey, row)).mapM
          (fun entry => CoreRecord.encodeCell? schema entry.2) with
  | none => simp [cellsResult] at encoded
  | some cells =>
      simp only [cellsResult, Option.bind_eq_bind, Option.bind] at encoded
      cases bodyResult : CoreFile.leafBody? 13 0 cells with
      | none => simp [CoreFile.tableLeafPage?, bodyResult] at encoded
      | some body =>
          simp only [CoreFile.tableLeafPage?, bodyResult, Option.bind_eq_bind,
            Option.bind, Option.some.injEq] at encoded
          subst page
          rcases CoreFile.leafBody_table_exact bodyResult with
            ⟨bodyBytes, fits⟩
          change CoreDecode.decodeTableInterior? body.bytes = none
          rw [bodyBytes]
          unfold CoreDecode.decodeTableInterior?
          have bodyLength :
              (PhysicalCodec.leafPageBody 0 cells).length =
                PhysicalCodec.pageSize := by
            simpa using PhysicalCodec.leafPageBody_length 0 cells fits
          rw [dif_pos bodyLength]
          unfold PhysicalCodec.leafPageBody PhysicalCodec.leafHeader
          rfl

theorem decodeTableInterior_tableLeafPage {cells : List (List UInt8)}
    {page : CoreFile.Page}
    (built : CoreFile.tableLeafPage? cells = some page) :
    CoreDecode.decodeTableInterior? page.bytes = none := by
  unfold CoreFile.tableLeafPage? at built
  cases bodyResult : CoreFile.leafBody? 13 0 cells with
  | none => simp [bodyResult] at built
  | some body =>
      simp only [bodyResult, Option.bind_eq_bind, Option.bind,
        Option.some.injEq] at built
      subst page
      rcases CoreFile.leafBody_table_exact bodyResult with ⟨bodyBytes, fits⟩
      change CoreDecode.decodeTableInterior? body.bytes = none
      rw [bodyBytes]
      unfold CoreDecode.decodeTableInterior?
      rw [dif_pos (by
        simpa using PhysicalCodec.leafPageBody_length 0 cells fits)]
      unfold PhysicalCodec.leafPageBody PhysicalCodec.leafHeader
      rfl

def encodeChunkNode (schema : Core.Schema) :
    PersistentPageTree.Node CoreChunkPageState.Chunk →
      Option (List NumberedPage)
  | .leaf pageId entries => do
      let page ← encodeChunkLeaf schema entries
      some [⟨pageId, page⟩]
  | .branch2 pageId left _ right => do
      let leftKey ← maximumChunkRowid? left
      let page ← RecursivePageBTree.interiorPage?
        [(left.rootId, leftKey)] right.rootId
      let leftPages ← encodeChunkNode schema left
      let rightPages ← encodeChunkNode schema right
      some (⟨pageId, page⟩ :: leftPages ++ rightPages)
  | .branch3 pageId left _ middle _ right => do
      let leftKey ← maximumChunkRowid? left
      let middleKey ← maximumChunkRowid? middle
      let page ← RecursivePageBTree.interiorPage?
        [(left.rootId, leftKey), (middle.rootId, middleKey)] right.rootId
      let leftPages ← encodeChunkNode schema left
      let middlePages ← encodeChunkNode schema middle
      let rightPages ← encodeChunkNode schema right
      some (⟨pageId, page⟩ :: leftPages ++ middlePages ++ rightPages)

theorem encodeChunkNode_pageNumbers (schema : Core.Schema)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (pages : List NumberedPage)
    (encoded : encodeChunkNode schema node = some pages) :
    pages.map NumberedPage.pageNumber = node.pageIds := by
  induction node generalizing pages with
  | leaf pageId entries =>
      unfold encodeChunkNode at encoded
      cases leafResult : encodeChunkLeaf schema entries with
      | none => simp [leafResult] at encoded
      | some page =>
          simp only [leafResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at encoded
          subst pages
          rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      unfold encodeChunkNode at encoded
      cases keyResult : maximumChunkRowid? left with
      | none => simp [keyResult] at encoded
      | some key =>
          simp only [keyResult, Option.bind_eq_bind, Option.bind] at encoded
          cases rootResult : RecursivePageBTree.interiorPage?
              [(left.rootId, key)] right.rootId with
          | none => simp [rootResult] at encoded
          | some root =>
              simp only [rootResult] at encoded
              cases leftResult : encodeChunkNode schema left with
              | none => simp [leftResult] at encoded
              | some leftPages =>
                  simp only [leftResult] at encoded
                  cases rightResult : encodeChunkNode schema right with
                  | none => simp [rightResult] at encoded
                  | some rightPages =>
                      simp only [rightResult, Option.some.injEq] at encoded
                      subst pages
                      simp only [List.map_cons, List.map_append,
                        PersistentPageTree.Node.pageIds]
                      rw [leftInduction leftPages leftResult,
                        rightInduction rightPages rightResult]
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      unfold encodeChunkNode at encoded
      cases leftKeyResult : maximumChunkRowid? left with
      | none => simp [leftKeyResult] at encoded
      | some leftKey =>
          simp only [leftKeyResult, Option.bind_eq_bind, Option.bind] at encoded
          cases middleKeyResult : maximumChunkRowid? middle with
          | none => simp [middleKeyResult] at encoded
          | some middleKey =>
              simp only [middleKeyResult] at encoded
              cases rootResult : RecursivePageBTree.interiorPage?
                  [(left.rootId, leftKey), (middle.rootId, middleKey)]
                    right.rootId with
              | none => simp [rootResult] at encoded
              | some root =>
                  simp only [rootResult] at encoded
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
                              simp only [List.map_cons, List.map_append,
                                PersistentPageTree.Node.pageIds]
                              rw [leftInduction leftPages leftResult,
                                middleInduction middlePages middleResult,
                                rightInduction rightPages rightResult]

def encodeChunkRoot (schema : Core.Schema) :
    PersistentPageTree.Node CoreChunkPageState.Chunk → Option NumberedPage
  | .leaf pageId entries => do
      let page ← encodeChunkLeaf schema entries
      some ⟨pageId, page⟩
  | .branch2 pageId left _ right => do
      let leftKey ← maximumChunkRowid? left
      let page ← RecursivePageBTree.interiorPage?
        [(left.rootId, leftKey)] right.rootId
      some ⟨pageId, page⟩
  | .branch3 pageId left _ middle _ right => do
      let leftKey ← maximumChunkRowid? left
      let middleKey ← maximumChunkRowid? middle
      let page ← RecursivePageBTree.interiorPage?
        [(left.rootId, leftKey), (middle.rootId, middleKey)] right.rootId
      some ⟨pageId, page⟩

theorem encodeChunkRoot_pageNumber (schema : Core.Schema)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (page : NumberedPage) (encoded : encodeChunkRoot schema node = some page) :
    page.pageNumber = node.rootId := by
  cases node with
  | leaf pageId entries =>
      change page.pageNumber = pageId
      simp only [encodeChunkRoot] at encoded
      cases pageResult : encodeChunkLeaf schema entries with
      | none => simp [pageResult] at encoded
      | some built =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at encoded
          subst page
          rfl
  | branch2 pageId left separator right =>
      change page.pageNumber = pageId
      simp only [encodeChunkRoot] at encoded
      cases keyResult : maximumChunkRowid? left with
      | none => simp [keyResult] at encoded
      | some key =>
          simp only [keyResult, Option.bind_eq_bind, Option.bind] at encoded
          cases rootResult : RecursivePageBTree.interiorPage?
              [(left.rootId, key)] right.rootId with
          | none =>
              rw [rootResult] at encoded
              contradiction
          | some built =>
              rw [rootResult] at encoded
              simp only [Option.some.injEq] at encoded
              subst page
              rfl
  | branch3 pageId left firstSeparator middle secondSeparator right =>
      change page.pageNumber = pageId
      simp only [encodeChunkRoot] at encoded
      cases leftResult : maximumChunkRowid? left with
      | none => simp [leftResult] at encoded
      | some leftKey =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at encoded
          cases middleResult : maximumChunkRowid? middle with
          | none => simp [middleResult] at encoded
          | some middleKey =>
              simp only [middleResult] at encoded
              cases rootResult : RecursivePageBTree.interiorPage?
                  [(left.rootId, leftKey), (middle.rootId, middleKey)]
                    right.rootId with
              | none =>
                  rw [rootResult] at encoded
                  contradiction
              | some built =>
                  rw [rootResult] at encoded
                  simp only [Option.some.injEq] at encoded
                  subst page
                  rfl

theorem boundedU32?_value {value : Nat} {bounded : FileFormat.U32Value}
    (success : RecursivePageBTree.boundedU32? value = some bounded) :
    bounded.val = value := by
  unfold RecursivePageBTree.boundedU32? at success
  split at success
  next =>
    injection success with equal
    subst bounded
    rfl
  next => contradiction

theorem interiorCell?_shape {child key : Nat} {cell : List UInt8}
    (success : RecursivePageBTree.interiorCell? child key = some cell) :
    ∃ childValue : FileFormat.U32Value,
      childValue.val = child ∧
      ∃ keyValue : FileFormat.U64Value, keyValue.val = key ∧
        cell = FileFormat.encodeU32Bytes childValue ++
          FileFormat.encodeVarint keyValue := by
  unfold RecursivePageBTree.interiorCell? at success
  cases childResult : RecursivePageBTree.boundedU32? child with
  | none => simp [childResult] at success
  | some childValue =>
      simp only [childResult, Option.bind_eq_bind, Option.bind] at success
      cases keyResult : RecursivePageBTree.boundedU64? key with
      | none => simp [keyResult] at success
      | some keyValue =>
          simp only [keyResult, Option.some.injEq] at success
          subst cell
          refine ⟨childValue, boundedU32?_value childResult, keyValue, ?_, rfl⟩
          unfold RecursivePageBTree.boundedU64? at keyResult
          split at keyResult
          next =>
            injection keyResult with equal
            subst keyValue
            rfl
          next => contradiction

theorem interiorChildren_interiorPage_one {child key right : Nat}
    {page : CoreFile.Page}
    (built : RecursivePageBTree.interiorPage? [(child, key)] right = some page) :
    CoreDecode.interiorChildren? page.bytes = some [child, right] := by
  unfold RecursivePageBTree.interiorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
      simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
      cases cellResult : RecursivePageBTree.interiorCell? child key with
      | none => simp [cellResult] at built
      | some cell =>
          rcases interiorCell?_shape cellResult with
            ⟨childValue, childEqual, keyValue, keyEqual, cellEqual⟩
          subst cell
          simp only [List.mapM_cons, cellResult, List.mapM_nil, pure,
            Pure.pure, Option.bind_eq_bind, Option.bind] at built
          split at built
          next fits =>
            injection built with equal
            subst page
            let encodedCell := FileFormat.encodeU32Bytes childValue ++
              FileFormat.encodeVarint keyValue
            let contentStart := PhysicalCodec.pageSize -
              (PhysicalCodec.cellBytes [encodedCell]).length
            let afterHeader := PhysicalCodec.leafPointers contentStart
                [encodedCell] ++
              List.replicate
                (contentStart -
                  (PhysicalTableBTree.interiorHeader 1 contentStart rightmost ++
                    PhysicalCodec.leafPointers contentStart
                      [encodedCell]).length) 0 ++
              PhysicalCodec.cellBytes [encodedCell]
            have bodyLayout :
                PhysicalTableBTree.interiorPageBody rightmost [encodedCell] =
                  5 :: 0 :: 0 ::
                    (PhysicalCodec.encodeU16Nat 1 ++
                      PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
                        (FileFormat.encodeU32Bytes rightmost ++
                          afterHeader)) := by
              unfold PhysicalTableBTree.interiorPageBody
                PhysicalTableBTree.interiorHeader
              simp only [List.cons_append, List.nil_append]
              rfl
            change CoreDecode.interiorChildren?
              (PhysicalTableBTree.interiorPageBody rightmost [encodedCell]) =
                some [child, right]
            unfold CoreDecode.interiorChildren?
            have bodyLength :
                (5 :: 0 :: 0 ::
                  (PhysicalCodec.encodeU16Nat 1 ++
                    PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
                      (FileFormat.encodeU32Bytes rightmost ++
                        afterHeader))).length = PhysicalCodec.pageSize := by
              rw [← bodyLayout]
              exact PhysicalTableBTree.interiorPageBody_length rightmost
                [encodedCell] fits
            simp only [bodyLayout]
            rw [if_pos (by simpa using bodyLength)]
            unfold PhysicalCodec.encodeU16Nat
            simp [FileFormat.encodeUnsignedFixed,
              FileFormat.decodeU16, FileFormat.encodeU32Bytes,
              FileFormat.decodeU32_encode]
            unfold afterHeader
            unfold PhysicalCodec.leafPointers PhysicalCodec.cellOffsetsFrom
            unfold PhysicalCodec.encodeU16Nat
            have contentBound : contentStart < 256 ^ 2 := by
              simpa using PhysicalCodec.contentStart_lt [encodedCell]
            have decodeOneOffset (suffix : List UInt8) :
                CoreDecode.decodeOffsetList 1
                  (FileFormat.encodeUnsignedFixed 2 contentStart ++ suffix) =
                    some [contentStart] := by
              unfold CoreDecode.decodeOffsetList
              rw [FileFormat.decodeUnsignedFixed_encode suffix contentBound]
              rfl
            simp only [PhysicalCodec.cellOffsetsFrom, List.flatMap_cons,
              List.flatMap_nil, List.append_nil, List.append_assoc,
              decodeOneOffset, Option.bind_eq_bind, Option.bind, List.mapM_cons,
              List.mapM_nil, pure, Pure.pure]
            have dropped := PhysicalTableBTree.interiorPageBody_drop_content
              rightmost [encodedCell] fits
            change (PhysicalTableBTree.interiorPageBody rightmost
              [encodedCell]).drop contentStart = [encodedCell].flatten at dropped
            simp only [bodyLayout] at dropped
            simp [PhysicalCodec.encodeU16Nat,
              FileFormat.encodeUnsignedFixed, FileFormat.encodeU32Bytes,
              afterHeader, PhysicalCodec.leafPointers,
              PhysicalCodec.cellOffsetsFrom] at dropped
            simp only [FileFormat.encodeUnsignedFixed, List.nil_append,
              List.singleton_append, List.cons_append, List.length_append,
              List.length_cons, List.length_nil]
            rw [dropped]
            have childDecoded := FileFormat.decodeU32_encode childValue
            have rightDecoded := FileFormat.decodeU32_encode rightmost
            simp [encodedCell, FileFormat.encodeU32Bytes, childDecoded,
              rightDecoded, childEqual, boundedU32?_value rightResult]
          next => contradiction

/-- The keyed routing decoder recovers the only separator and both children
from a generated two-way table interior page. -/
theorem decodeTableInterior_interiorPage_one {child key right : Nat}
    {page : CoreFile.Page} (childPositive : 0 < child)
    (keyBound : key < 2 ^ 64)
    (built : RecursivePageBTree.interiorPage? [(child, key)] right = some page) :
    CoreDecode.decodeTableInterior? page.bytes = some
      ([(child, FileFormat.signedIntegerFromUnsigned .eight
        ⟨key, by simpa [FileFormat.IntegerWidth.modulus] using keyBound⟩)], right) := by
  unfold RecursivePageBTree.interiorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
      simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
      cases cellResult : RecursivePageBTree.interiorCell? child key with
      | none => simp [cellResult] at built
      | some cell =>
          rcases interiorCell?_shape cellResult with
            ⟨childValue, childEqual, keyValue, keyEqual, cellEqual⟩
          subst cell
          simp only [List.mapM_cons, cellResult, List.mapM_nil, pure,
            Pure.pure, Option.bind_eq_bind, Option.bind] at built
          split at built
          next fits =>
            injection built with equal
            subst page
            let encodedCell := FileFormat.encodeU32Bytes childValue ++
              FileFormat.encodeVarint keyValue
            let cells := [encodedCell]
            let contentStart := PhysicalCodec.pageSize -
              (PhysicalCodec.cellBytes cells).length
            let afterHeader := PhysicalCodec.leafPointers contentStart cells ++
              List.replicate
                (contentStart -
                  (PhysicalTableBTree.interiorHeader 1 contentStart rightmost ++
                    PhysicalCodec.leafPointers contentStart cells).length) 0 ++
              PhysicalCodec.cellBytes cells
            have bodyLayout :
                PhysicalTableBTree.interiorPageBody rightmost cells =
                  PhysicalTableBTree.interiorHeader 1 contentStart rightmost ++
                    afterHeader := by
              unfold PhysicalTableBTree.interiorPageBody afterHeader cells
              rfl
            have bodyLength :
                (PhysicalTableBTree.interiorPageBody rightmost cells).length =
                  PhysicalCodec.pageSize :=
              PhysicalTableBTree.interiorPageBody_length rightmost cells fits
            have countBound : 1 < 256 ^ 2 := by decide
            have contentBound : contentStart < 256 ^ 2 := by
              simpa [cells] using PhysicalCodec.contentStart_lt cells
            let common : FileFormat.BTreePageHeaderCommon := {
              firstFreeblock := ⟨0, by decide⟩
              cellCount := ⟨1, by decide⟩
              cellContentStart := ⟨contentStart, by
                simpa using contentBound⟩
              fragmentedFreeBytes := 0 }
            have headerEncoding :
                FileFormat.encodeBTreePageHeader
                    (.interiorTable common rightmost) =
                  PhysicalTableBTree.interiorHeader 1 contentStart rightmost := by
              rw [FileFormat.encodeBTreePageHeader_interiorTable]
              rw [FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed,
                FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed,
                FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed]
              dsimp [common]
              simp [PhysicalTableBTree.interiorHeader,
                PhysicalCodec.encodeU16Nat, FileFormat.encodeUnsignedFixed]
            have decodeOneOffset (suffix : List UInt8) :
                CoreDecode.decodeOffsets 1
                    (FileFormat.encodeUnsignedFixed 2 contentStart ++ suffix) =
                  some ([contentStart], suffix) := by
              unfold CoreDecode.decodeOffsets
              rw [FileFormat.decodeUnsignedFixed_encode suffix contentBound]
              rfl
            have dropped := PhysicalTableBTree.interiorPageBody_drop_content
              rightmost cells fits
            change (PhysicalTableBTree.interiorPageBody rightmost cells).drop
              contentStart = cells.flatten at dropped
            have droppedCell :
                (PhysicalTableBTree.interiorPageBody rightmost cells).drop
                    contentStart = encodedCell := by
              simpa [cells, PhysicalCodec.cellBytes] using dropped
            let childPage : FileFormat.PageNumber :=
              ⟨childValue, by rw [childEqual]; exact childPositive⟩
            let signedKey := FileFormat.signedIntegerFromUnsigned .eight keyValue
            let typedCell : FileFormat.InteriorTableCell :=
              ⟨childPage, signedKey⟩
            have typedEncoding : typedCell.encode = encodedCell := by
              change FileFormat.encodeU32Bytes childValue ++
                  FileFormat.encodeVarint
                    (FileFormat.signedInteger64Bits signedKey) = encodedCell
              have bitsEqual :
                  FileFormat.signedInteger64Bits signedKey = keyValue := by
                apply Fin.ext
                exact FileFormat.SignedInteger.toUnsigned_fromUnsigned
                  .eight keyValue
              rw [bitsEqual]
            have keyValueEq : keyValue =
                ⟨key, by simpa [FileFormat.IntegerWidth.modulus] using keyBound⟩ := by
              apply Fin.ext
              exact keyEqual
            change CoreDecode.decodeTableInterior?
              (PhysicalTableBTree.interiorPageBody rightmost cells) = _
            unfold CoreDecode.decodeTableInterior?
            rw [dif_pos bodyLength]
            have headerDecoded : FileFormat.decodeBTreePageHeader
                (PhysicalTableBTree.interiorPageBody rightmost cells) =
                  some (.interiorTable common rightmost, afterHeader) := by
              rw [bodyLayout, ← headerEncoding,
                FileFormat.decodeBTreePageHeader_encode]
            rw [headerDecoded]
            simp only [Option.bind_eq_bind, Option.bind]
            simp only [common]
            unfold afterHeader PhysicalCodec.leafPointers
              PhysicalCodec.cellOffsetsFrom cells
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
              List.append_assoc, PhysicalCodec.encodeU16Nat]
            rw [decodeOneOffset]
            simp only [Option.bind_eq_bind, Option.bind, List.mapM_cons,
              List.mapM_nil, pure, Pure.pure]
            have contentWithin : contentStart <
                (PhysicalTableBTree.interiorPageBody rightmost
                  [encodedCell]).length := by
              rw [show (PhysicalTableBTree.interiorPageBody rightmost
                [encodedCell]).length = PhysicalCodec.pageSize from by
                  simpa [cells] using bodyLength]
              unfold contentStart
              have cellBytesPositive :
                  0 < (PhysicalCodec.cellBytes cells).length := by
                simp [cells, encodedCell, PhysicalCodec.cellBytes,
                  FileFormat.encodeU32Bytes]
              have pageSizePositive : 0 < PhysicalCodec.pageSize := by decide
              omega
            rw [dif_pos contentWithin]
            rw [show (PhysicalTableBTree.interiorPageBody rightmost
              [encodedCell]).drop contentStart = encodedCell from by
                simpa [cells] using droppedCell, ← typedEncoding]
            have typedDecoded : FileFormat.decodeInteriorTableCell
                typedCell.encode = some (typedCell, []) := by
              simpa using
                FileFormat.decodeInteriorTableCell_encode typedCell []
            rw [typedDecoded]
            simp only [Option.bind_eq_bind, Option.bind]
            subst keyValue
            have signedKeyExpected : signedKey =
                FileFormat.signedIntegerFromUnsigned .eight
                  ⟨key, by simpa [FileFormat.IntegerWidth.modulus] using
                    keyBound⟩ := by
              apply FileFormat.SignedInteger.ext
              rfl
            simp [typedCell, childPage, childEqual,
              signedKeyExpected, boundedU32?_value rightResult]
          next => contradiction

theorem interiorChildren_interiorPage_two {firstChild firstKey secondChild
    secondKey right : Nat} {page : CoreFile.Page}
    (built : RecursivePageBTree.interiorPage?
      [(firstChild, firstKey), (secondChild, secondKey)] right = some page) :
    CoreDecode.interiorChildren? page.bytes =
      some [firstChild, secondChild, right] := by
  unfold RecursivePageBTree.interiorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
      simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
      cases firstResult : RecursivePageBTree.interiorCell? firstChild firstKey with
      | none => simp [firstResult] at built
      | some firstCell =>
          cases secondResult : RecursivePageBTree.interiorCell?
              secondChild secondKey with
          | none => simp [firstResult, secondResult] at built
          | some secondCell =>
              rcases interiorCell?_shape firstResult with
                ⟨firstValue, firstEqual, firstKeyValue, _, firstCellEqual⟩
              rcases interiorCell?_shape secondResult with
                ⟨secondValue, secondEqual, secondKeyValue, _, secondCellEqual⟩
              subst firstCell
              subst secondCell
              simp only [List.mapM_cons, firstResult, secondResult,
                List.mapM_nil, pure, Pure.pure, Option.bind_eq_bind,
                Option.bind] at built
              split at built
              next fits =>
                injection built with equal
                subst page
                let encodedFirst := FileFormat.encodeU32Bytes firstValue ++
                  FileFormat.encodeVarint firstKeyValue
                let encodedSecond := FileFormat.encodeU32Bytes secondValue ++
                  FileFormat.encodeVarint secondKeyValue
                let cells := [encodedFirst, encodedSecond]
                change PhysicalTableBTree.InteriorPageFit cells at fits
                let contentStart := PhysicalCodec.pageSize -
                  (PhysicalCodec.cellBytes cells).length
                let secondStart := contentStart + encodedFirst.length
                let afterHeader := PhysicalCodec.leafPointers contentStart cells ++
                  List.replicate
                    (contentStart -
                      (PhysicalTableBTree.interiorHeader 2 contentStart
                        rightmost ++
                        PhysicalCodec.leafPointers contentStart cells).length) 0 ++
                  PhysicalCodec.cellBytes cells
                have bodyLayout :
                    PhysicalTableBTree.interiorPageBody rightmost cells =
                      5 :: 0 :: 0 ::
                        (PhysicalCodec.encodeU16Nat 2 ++
                          PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
                            (FileFormat.encodeU32Bytes rightmost ++
                              afterHeader)) := by
                  unfold PhysicalTableBTree.interiorPageBody
                    PhysicalTableBTree.interiorHeader
                  simp only [List.cons_append, List.nil_append]
                  rfl
                change CoreDecode.interiorChildren?
                  (PhysicalTableBTree.interiorPageBody rightmost cells) =
                    some [firstChild, secondChild, right]
                unfold CoreDecode.interiorChildren?
                have bodyLength :
                    (5 :: 0 :: 0 ::
                      (PhysicalCodec.encodeU16Nat 2 ++
                        PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
                          (FileFormat.encodeU32Bytes rightmost ++
                            afterHeader))).length = PhysicalCodec.pageSize := by
                  rw [← bodyLayout]
                  exact PhysicalTableBTree.interiorPageBody_length rightmost
                    cells fits
                simp only [bodyLayout]
                rw [if_pos (by simpa using bodyLength)]
                unfold PhysicalCodec.encodeU16Nat
                simp [FileFormat.encodeUnsignedFixed, FileFormat.decodeU16,
                  FileFormat.encodeU32Bytes, FileFormat.decodeU32_encode]
                unfold afterHeader PhysicalCodec.leafPointers
                  PhysicalCodec.cellOffsetsFrom PhysicalCodec.encodeU16Nat
                have firstBound : contentStart < 256 ^ 2 := by
                  simpa [cells] using PhysicalCodec.contentStart_lt cells
                have secondBound : secondStart < 256 ^ 2 := by
                  have contentLe : (PhysicalCodec.cellBytes cells).length ≤
                      PhysicalCodec.pageSize := by
                    unfold PhysicalTableBTree.InteriorPageFit at fits
                    omega
                  have firstLengthLe : encodedFirst.length ≤
                      (PhysicalCodec.cellBytes cells).length := by
                    simp [cells, PhysicalCodec.cellBytes]
                  have contentIdentity : contentStart +
                      (PhysicalCodec.cellBytes cells).length =
                        PhysicalCodec.pageSize := by
                    unfold contentStart
                    exact Nat.sub_add_cancel contentLe
                  calc
                    secondStart ≤ contentStart +
                        (PhysicalCodec.cellBytes cells).length := by
                      unfold secondStart
                      exact Nat.add_le_add_left firstLengthLe contentStart
                    _ = PhysicalCodec.pageSize := contentIdentity
                    _ < 256 ^ 2 := by decide
                have decodeTwoOffsets (suffix : List UInt8) :
                    CoreDecode.decodeOffsetList 2
                      (FileFormat.encodeUnsignedFixed 2 contentStart ++
                        FileFormat.encodeUnsignedFixed 2 secondStart ++ suffix) =
                      some [contentStart, secondStart] := by
                  unfold CoreDecode.decodeOffsetList
                  simp only [List.append_assoc,
                    FileFormat.decodeUnsignedFixed_encode _ firstBound,
                    Option.bind_eq_bind, Option.bind]
                  unfold CoreDecode.decodeOffsetList
                  rw [FileFormat.decodeUnsignedFixed_encode suffix secondBound]
                  rfl
                have decodeTwoOffsetsExpanded (suffix : List UInt8) :
                    CoreDecode.decodeOffsetList 2
                      (UInt8.ofNat (contentStart / 256 % 256) ::
                        UInt8.ofNat (contentStart % 256) ::
                        UInt8.ofNat (secondStart / 256 % 256) ::
                        UInt8.ofNat (secondStart % 256) :: suffix) =
                      some [contentStart, secondStart] := by
                  simpa [FileFormat.encodeUnsignedFixed] using
                    decodeTwoOffsets suffix
                have decodeTwoOffsetsConcrete (suffix : List UInt8) :
                    CoreDecode.decodeOffsetList 2
                      (UInt8.ofNat (contentStart / 256 % 256) ::
                        UInt8.ofNat (contentStart % 256) ::
                        UInt8.ofNat
                          ((contentStart + encodedFirst.length) / 256 % 256) ::
                        UInt8.ofNat
                          ((contentStart + encodedFirst.length) % 256) :: suffix) =
                      some [contentStart, contentStart + encodedFirst.length] := by
                  simpa [secondStart] using decodeTwoOffsetsExpanded suffix
                have decodeTwoOffsetsRight (suffix : List UInt8) :
                    CoreDecode.decodeOffsetList 2
                      (FileFormat.encodeUnsignedFixed 2 contentStart ++
                        (FileFormat.encodeUnsignedFixed 2
                          (contentStart + encodedFirst.length) ++ suffix)) =
                      some [contentStart, contentStart + encodedFirst.length] := by
                  simpa [secondStart, List.append_assoc] using
                    decodeTwoOffsets suffix
                simp only [cells, PhysicalCodec.cellOffsetsFrom,
                  List.flatMap_cons, List.flatMap_nil, List.append_nil,
                  List.append_assoc]
                rw [decodeTwoOffsetsRight]
                simp only [Option.bind_eq_bind, Option.bind]
                simp only [cells, PhysicalCodec.cellOffsetsFrom,
                  List.flatMap_cons, List.flatMap_nil, List.append_nil,
                  List.append_assoc, decodeTwoOffsets,
                  decodeTwoOffsetsExpanded, decodeTwoOffsetsConcrete,
                  Option.bind_eq_bind,
                  Option.bind, List.mapM_cons, List.mapM_nil, pure, Pure.pure]
                have droppedFirst :=
                  PhysicalTableBTree.interiorPageBody_drop_content rightmost
                    cells fits
                change (PhysicalTableBTree.interiorPageBody rightmost cells).drop
                    contentStart = cells.flatten at droppedFirst
                have droppedSecond :
                    (PhysicalTableBTree.interiorPageBody rightmost cells).drop
                      secondStart = encodedSecond := by
                  rw [show secondStart = contentStart + encodedFirst.length from rfl,
                    ← List.drop_drop, droppedFirst]
                  simp [cells, PhysicalCodec.cellBytes]
                simp only [bodyLayout] at droppedFirst droppedSecond
                simp [PhysicalCodec.encodeU16Nat,
                  FileFormat.encodeUnsignedFixed, FileFormat.encodeU32Bytes,
                  afterHeader, PhysicalCodec.leafPointers,
                  PhysicalCodec.cellOffsetsFrom, cells] at droppedFirst droppedSecond
                simp only [FileFormat.encodeUnsignedFixed, List.nil_append,
                  List.singleton_append, List.cons_append, List.length_append,
                  List.length_cons, List.length_nil]
                rw [droppedFirst, droppedSecond]
                have firstDecoded := FileFormat.decodeU32_encode firstValue
                have secondDecoded := FileFormat.decodeU32_encode secondValue
                have rightDecoded := FileFormat.decodeU32_encode rightmost
                simp [encodedFirst, encodedSecond, FileFormat.encodeU32Bytes,
                  firstDecoded, secondDecoded, rightDecoded, firstEqual,
                  secondEqual, boundedU32?_value rightResult]
              next => injection built

/-- The keyed routing decoder recovers both separators and all three children
from a generated three-way table interior page. -/
theorem decodeTableInterior_interiorPage_two
    {firstChild firstKey secondChild secondKey right : Nat}
    {page : CoreFile.Page} (firstPositive : 0 < firstChild)
    (secondPositive : 0 < secondChild) (firstKeyBound : firstKey < 2 ^ 64)
    (secondKeyBound : secondKey < 2 ^ 64)
    (built : RecursivePageBTree.interiorPage?
      [(firstChild, firstKey), (secondChild, secondKey)] right = some page) :
    CoreDecode.decodeTableInterior? page.bytes = some
      ([(firstChild, FileFormat.signedIntegerFromUnsigned .eight
          ⟨firstKey, by simpa [FileFormat.IntegerWidth.modulus] using
            firstKeyBound⟩),
        (secondChild, FileFormat.signedIntegerFromUnsigned .eight
          ⟨secondKey, by simpa [FileFormat.IntegerWidth.modulus] using
            secondKeyBound⟩)], right) := by
  unfold RecursivePageBTree.interiorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
      simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
      cases firstResult : RecursivePageBTree.interiorCell? firstChild firstKey with
      | none => simp [firstResult] at built
      | some firstCell =>
          cases secondResult : RecursivePageBTree.interiorCell?
              secondChild secondKey with
          | none => simp [firstResult, secondResult] at built
          | some secondCell =>
              rcases interiorCell?_shape firstResult with
                ⟨firstValue, firstEqual, firstKeyValue, firstKeyEqual,
                  firstCellEqual⟩
              rcases interiorCell?_shape secondResult with
                ⟨secondValue, secondEqual, secondKeyValue, secondKeyEqual,
                  secondCellEqual⟩
              subst firstCell
              subst secondCell
              simp only [List.mapM_cons, firstResult, secondResult,
                List.mapM_nil, pure, Pure.pure, Option.bind_eq_bind,
                Option.bind] at built
              split at built
              next fits =>
                injection built with equal
                subst page
                let encodedFirst := FileFormat.encodeU32Bytes firstValue ++
                  FileFormat.encodeVarint firstKeyValue
                let encodedSecond := FileFormat.encodeU32Bytes secondValue ++
                  FileFormat.encodeVarint secondKeyValue
                let cells := [encodedFirst, encodedSecond]
                change PhysicalTableBTree.InteriorPageFit cells at fits
                let contentStart := PhysicalCodec.pageSize -
                  (PhysicalCodec.cellBytes cells).length
                let secondStart := contentStart + encodedFirst.length
                let afterHeader := PhysicalCodec.leafPointers contentStart cells ++
                  List.replicate
                    (contentStart -
                      (PhysicalTableBTree.interiorHeader 2 contentStart
                        rightmost ++
                        PhysicalCodec.leafPointers contentStart cells).length) 0 ++
                  PhysicalCodec.cellBytes cells
                have bodyLayout :
                    PhysicalTableBTree.interiorPageBody rightmost cells =
                      PhysicalTableBTree.interiorHeader 2 contentStart
                        rightmost ++ afterHeader := by
                  unfold PhysicalTableBTree.interiorPageBody afterHeader cells
                  rfl
                have bodyLength :
                    (PhysicalTableBTree.interiorPageBody rightmost cells).length =
                      PhysicalCodec.pageSize :=
                  PhysicalTableBTree.interiorPageBody_length rightmost cells fits
                have firstBound : contentStart < 256 ^ 2 := by
                  simpa [cells] using PhysicalCodec.contentStart_lt cells
                have contentLe : (PhysicalCodec.cellBytes cells).length ≤
                    PhysicalCodec.pageSize := by
                  unfold PhysicalTableBTree.InteriorPageFit at fits
                  omega
                have contentIdentity : contentStart +
                    (PhysicalCodec.cellBytes cells).length =
                      PhysicalCodec.pageSize := by
                  unfold contentStart
                  exact Nat.sub_add_cancel contentLe
                have secondBound : secondStart < 256 ^ 2 := by
                  have firstLengthLe : encodedFirst.length ≤
                      (PhysicalCodec.cellBytes cells).length := by
                    simp [cells, PhysicalCodec.cellBytes]
                  calc
                    secondStart ≤ contentStart +
                        (PhysicalCodec.cellBytes cells).length := by
                      unfold secondStart
                      exact Nat.add_le_add_left firstLengthLe contentStart
                    _ = PhysicalCodec.pageSize := contentIdentity
                    _ < 256 ^ 2 := by decide
                let common : FileFormat.BTreePageHeaderCommon := {
                  firstFreeblock := ⟨0, by decide⟩
                  cellCount := ⟨2, by decide⟩
                  cellContentStart := ⟨contentStart, by
                    simpa using firstBound⟩
                  fragmentedFreeBytes := 0 }
                have headerEncoding :
                    FileFormat.encodeBTreePageHeader
                        (.interiorTable common rightmost) =
                      PhysicalTableBTree.interiorHeader 2 contentStart
                        rightmost := by
                  rw [FileFormat.encodeBTreePageHeader_interiorTable]
                  rw [FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed,
                    FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed,
                    FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed]
                  dsimp [common]
                  simp [PhysicalTableBTree.interiorHeader,
                    PhysicalCodec.encodeU16Nat,
                    FileFormat.encodeUnsignedFixed]
                have decodeTwoOffsets (suffix : List UInt8) :
                    CoreDecode.decodeOffsets 2
                      (FileFormat.encodeUnsignedFixed 2 contentStart ++
                        FileFormat.encodeUnsignedFixed 2 secondStart ++ suffix) =
                      some ([contentStart, secondStart], suffix) := by
                  unfold CoreDecode.decodeOffsets
                  simp only [List.append_assoc]
                  rw [FileFormat.decodeUnsignedFixed_encode _ firstBound]
                  simp only [Option.bind_eq_bind, Option.bind]
                  unfold CoreDecode.decodeOffsets
                  rw [FileFormat.decodeUnsignedFixed_encode suffix secondBound]
                  rfl
                have decodeTwoOffsetsConcrete (suffix : List UInt8) :
                    CoreDecode.decodeOffsets 2
                      (FileFormat.encodeUnsignedFixed 2 contentStart ++
                        FileFormat.encodeUnsignedFixed 2
                          (contentStart + encodedFirst.length) ++ suffix) =
                      some ([contentStart,
                        contentStart + encodedFirst.length], suffix) := by
                  simpa [secondStart] using decodeTwoOffsets suffix
                have decodeTwoOffsetsRight (suffix : List UInt8) :
                    CoreDecode.decodeOffsets 2
                      (FileFormat.encodeUnsignedFixed 2 contentStart ++
                        (FileFormat.encodeUnsignedFixed 2
                          (contentStart + encodedFirst.length) ++ suffix)) =
                      some ([contentStart,
                        contentStart + encodedFirst.length], suffix) := by
                  simpa [List.append_assoc] using
                    decodeTwoOffsetsConcrete suffix
                have droppedFirst :=
                  PhysicalTableBTree.interiorPageBody_drop_content rightmost
                    cells fits
                change (PhysicalTableBTree.interiorPageBody rightmost cells).drop
                    contentStart = cells.flatten at droppedFirst
                have firstDrop :
                    (PhysicalTableBTree.interiorPageBody rightmost cells).drop
                      contentStart = encodedFirst ++ encodedSecond := by
                  simpa [cells, PhysicalCodec.cellBytes] using droppedFirst
                have secondDrop :
                    (PhysicalTableBTree.interiorPageBody rightmost cells).drop
                      secondStart = encodedSecond := by
                  rw [show secondStart = contentStart + encodedFirst.length from
                    rfl, ← List.drop_drop, firstDrop]
                  simp
                let firstPage : FileFormat.PageNumber :=
                  ⟨firstValue, by rw [firstEqual]; exact firstPositive⟩
                let secondPage : FileFormat.PageNumber :=
                  ⟨secondValue, by rw [secondEqual]; exact secondPositive⟩
                let firstSigned :=
                  FileFormat.signedIntegerFromUnsigned .eight firstKeyValue
                let secondSigned :=
                  FileFormat.signedIntegerFromUnsigned .eight secondKeyValue
                let typedFirst : FileFormat.InteriorTableCell :=
                  ⟨firstPage, firstSigned⟩
                let typedSecond : FileFormat.InteriorTableCell :=
                  ⟨secondPage, secondSigned⟩
                have firstEncoding : typedFirst.encode = encodedFirst := by
                  change FileFormat.encodeU32Bytes firstValue ++
                    FileFormat.encodeVarint
                      (FileFormat.signedInteger64Bits firstSigned) = encodedFirst
                  have bitsEqual : FileFormat.signedInteger64Bits firstSigned =
                      firstKeyValue := by
                    apply Fin.ext
                    exact FileFormat.SignedInteger.toUnsigned_fromUnsigned
                      .eight firstKeyValue
                  rw [bitsEqual]
                have secondEncoding : typedSecond.encode = encodedSecond := by
                  change FileFormat.encodeU32Bytes secondValue ++
                    FileFormat.encodeVarint
                      (FileFormat.signedInteger64Bits secondSigned) = encodedSecond
                  have bitsEqual : FileFormat.signedInteger64Bits secondSigned =
                      secondKeyValue := by
                    apply Fin.ext
                    exact FileFormat.SignedInteger.toUnsigned_fromUnsigned
                      .eight secondKeyValue
                  rw [bitsEqual]
                have firstDecoded : FileFormat.decodeInteriorTableCell
                    (typedFirst.encode ++ encodedSecond) =
                      some (typedFirst, encodedSecond) :=
                  FileFormat.decodeInteriorTableCell_encode _ _
                have secondDecoded : FileFormat.decodeInteriorTableCell
                    typedSecond.encode = some (typedSecond, []) := by
                  simpa using FileFormat.decodeInteriorTableCell_encode
                    typedSecond []
                have firstKeyValueEq : firstKeyValue =
                    ⟨firstKey, by simpa [FileFormat.IntegerWidth.modulus]
                      using firstKeyBound⟩ := by
                  apply Fin.ext
                  exact firstKeyEqual
                have secondKeyValueEq : secondKeyValue =
                    ⟨secondKey, by simpa [FileFormat.IntegerWidth.modulus]
                      using secondKeyBound⟩ := by
                  apply Fin.ext
                  exact secondKeyEqual
                change CoreDecode.decodeTableInterior?
                  (PhysicalTableBTree.interiorPageBody rightmost cells) = _
                unfold CoreDecode.decodeTableInterior?
                rw [dif_pos bodyLength]
                have headerDecoded : FileFormat.decodeBTreePageHeader
                    (PhysicalTableBTree.interiorPageBody rightmost cells) =
                      some (.interiorTable common rightmost, afterHeader) := by
                  rw [bodyLayout, ← headerEncoding,
                    FileFormat.decodeBTreePageHeader_encode]
                rw [headerDecoded]
                simp only [Option.bind_eq_bind, Option.bind, common]
                unfold afterHeader PhysicalCodec.leafPointers
                  PhysicalCodec.cellOffsetsFrom cells
                simp only [List.flatMap_cons, List.flatMap_nil,
                  List.append_nil, List.append_assoc,
                  PhysicalCodec.encodeU16Nat,
                  PhysicalCodec.cellOffsetsFrom]
                rw [decodeTwoOffsetsRight]
                simp only [Option.bind_eq_bind, Option.bind, List.mapM_cons,
                  List.mapM_nil, pure, Pure.pure]
                have contentWithin : contentStart <
                    (PhysicalTableBTree.interiorPageBody rightmost cells).length := by
                  rw [bodyLength, ← contentIdentity]
                  have bytesPositive :
                      0 < (PhysicalCodec.cellBytes cells).length := by
                    simp [cells, encodedFirst, PhysicalCodec.cellBytes,
                      FileFormat.encodeU32Bytes]
                  omega
                have secondWithin : secondStart <
                    (PhysicalTableBTree.interiorPageBody rightmost cells).length := by
                  rw [bodyLength, ← contentIdentity]
                  unfold secondStart
                  have firstLengthLt : encodedFirst.length <
                      (PhysicalCodec.cellBytes cells).length := by
                    simp [cells, encodedSecond, PhysicalCodec.cellBytes,
                      FileFormat.encodeU32Bytes]
                  omega
                have secondWithinTyped :
                    contentStart + typedFirst.encode.length <
                      (PhysicalTableBTree.interiorPageBody rightmost
                        [typedFirst.encode, encodedSecond]).length := by
                  rw [firstEncoding]
                  simpa [cells, secondStart] using secondWithin
                have secondDropTyped :
                    (PhysicalTableBTree.interiorPageBody rightmost
                      [typedFirst.encode, encodedSecond]).drop
                        (contentStart + typedFirst.encode.length) =
                      encodedSecond := by
                  rw [firstEncoding]
                  simpa [cells, secondStart] using secondDrop
                rw [dif_pos contentWithin, firstDrop, ← firstEncoding,
                  firstDecoded]
                simp only [Option.bind_eq_bind, Option.bind]
                rw [dif_pos secondWithinTyped, secondDropTyped,
                  ← secondEncoding,
                  secondDecoded]
                simp only [Option.bind_eq_bind, Option.bind]
                subst firstKeyValue
                subst secondKeyValue
                have firstSignedExpected : firstSigned =
                    FileFormat.signedIntegerFromUnsigned .eight
                      ⟨firstKey, by simpa [FileFormat.IntegerWidth.modulus]
                        using firstKeyBound⟩ := by
                  apply FileFormat.SignedInteger.ext
                  rfl
                have secondSignedExpected : secondSigned =
                    FileFormat.signedIntegerFromUnsigned .eight
                      ⟨secondKey, by simpa [FileFormat.IntegerWidth.modulus]
                        using secondKeyBound⟩ := by
                  apply FileFormat.SignedInteger.ext
                  rfl
                simp [typedFirst, typedSecond, firstPage, secondPage,
                  firstEqual, secondEqual, firstSignedExpected,
                  secondSignedExpected, boundedU32?_value rightResult]
              next => contradiction

theorem decodeTableInterior_encodeChunkRoot_branch2 (schema : Core.Schema)
    (pageId : Nat) (left : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (separator : Nat) (right : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (root : NumberedPage) (leftPositive : 0 < left.rootId)
    (built : encodeChunkRoot schema
      (.branch2 pageId left separator right) = some root) :
    ∃ boundary,
      (CoreChunkPageState.Node.rows left).getLast? = some boundary ∧
      CoreDecode.decodeTableInterior? root.page.bytes =
        some ([(left.rootId, boundary.rowid)], right.rootId) := by
  simp only [encodeChunkRoot] at built
  cases keyResult : maximumChunkRowid? left with
  | none => simp [keyResult] at built
  | some key =>
      simp only [keyResult, Option.bind_eq_bind, Option.bind] at built
      cases pageResult : RecursivePageBTree.interiorPage?
          [(left.rootId, key)] right.rootId with
      | none => simp [pageResult] at built
      | some page =>
          simp only [pageResult, Option.some.injEq] at built
          subst root
          rcases maximumChunkRowid?_witness keyResult with
            ⟨boundary, boundaryLast, rfl⟩
          refine ⟨boundary, boundaryLast, ?_⟩
          have keyBound : boundary.rowid.toUnsigned < 2 ^ 64 := by
            simpa [FileFormat.IntegerWidth.modulus] using
              boundary.rowid.toUnsigned_lt
          rw [decodeTableInterior_interiorPage_one leftPositive keyBound
            pageResult]
          simp [FileFormat.signedIntegerFromUnsigned_toUnsigned]

theorem decodeTableInterior_encodeChunkRoot_branch3 (schema : Core.Schema)
    (pageId : Nat) (left : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (firstSeparator : Nat)
    (middle : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (secondSeparator : Nat)
    (right : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (root : NumberedPage) (leftPositive : 0 < left.rootId)
    (middlePositive : 0 < middle.rootId)
    (built : encodeChunkRoot schema
      (.branch3 pageId left firstSeparator middle secondSeparator right) =
        some root) :
    ∃ leftBoundary middleBoundary,
      (CoreChunkPageState.Node.rows left).getLast? = some leftBoundary ∧
      (CoreChunkPageState.Node.rows middle).getLast? = some middleBoundary ∧
      CoreDecode.decodeTableInterior? root.page.bytes = some
        ([(left.rootId, leftBoundary.rowid),
          (middle.rootId, middleBoundary.rowid)], right.rootId) := by
  simp only [encodeChunkRoot] at built
  cases leftKeyResult : maximumChunkRowid? left with
  | none => simp [leftKeyResult] at built
  | some leftKey =>
      simp only [leftKeyResult, Option.bind_eq_bind, Option.bind] at built
      cases middleKeyResult : maximumChunkRowid? middle with
      | none => simp [middleKeyResult] at built
      | some middleKey =>
          simp only [middleKeyResult] at built
          cases pageResult : RecursivePageBTree.interiorPage?
              [(left.rootId, leftKey), (middle.rootId, middleKey)]
                right.rootId with
          | none => simp [pageResult] at built
          | some page =>
              simp only [pageResult, Option.some.injEq] at built
              subst root
              rcases maximumChunkRowid?_witness leftKeyResult with
                ⟨leftBoundary, leftLast, rfl⟩
              rcases maximumChunkRowid?_witness middleKeyResult with
                ⟨middleBoundary, middleLast, rfl⟩
              refine ⟨leftBoundary, middleBoundary, leftLast, middleLast, ?_⟩
              have leftKeyBound : leftBoundary.rowid.toUnsigned < 2 ^ 64 := by
                simpa [FileFormat.IntegerWidth.modulus] using
                  leftBoundary.rowid.toUnsigned_lt
              have middleKeyBound :
                  middleBoundary.rowid.toUnsigned < 2 ^ 64 := by
                simpa [FileFormat.IntegerWidth.modulus] using
                  middleBoundary.rowid.toUnsigned_lt
              rw [decodeTableInterior_interiorPage_two leftPositive
                middlePositive leftKeyBound middleKeyBound pageResult]
              simp [FileFormat.signedIntegerFromUnsigned_toUnsigned]

/-- A page source contains an encoded page set when reading every advertised
page identity returns exactly the bytes emitted for that identity. -/
def PageSourceContains (source : CoreDecode.PageSource)
    (pages : List NumberedPage) : Prop :=
  ∀ numbered ∈ pages,
    source.readPage numbered.pageNumber = some numbered.page.bytes

theorem PageSourceContains.ofReadsRange (source : CoreDecode.PageSource) :
    ∀ (start : Nat) (pages : List NumberedPage),
      pages.map NumberedPage.pageNumber = List.range' start pages.length →
      CoreDecode.ReadsPagesFrom source start
        (pages.map NumberedPage.page) →
      PageSourceContains source pages
  | _, [], _, _ => by simp [PageSourceContains]
  | start, page :: pages, numbers, reads => by
      change page.pageNumber :: pages.map NumberedPage.pageNumber =
        start :: List.range' (start + 1) pages.length at numbers
      injection numbers with pageNumber tailNumbers
      have headRead : source.readPage start = some page.page.bytes := by
        have available := reads 0 (by simp)
        simpa using available
      have tailReads : CoreDecode.ReadsPagesFrom source (start + 1)
          (pages.map NumberedPage.page) := by
        have remaining := CoreDecode.ReadsPagesFrom.right
          (left := [page.page]) (right := pages.map NumberedPage.page) reads
        simpa using remaining
      have tailContains := ofReadsRange source (start + 1) pages tailNumbers
        tailReads
      intro numbered member
      simp only [List.mem_cons] at member
      rcases member with equal | later
      · subst numbered
        simpa [pageNumber] using headRead
      · exact tailContains numbered later

/- The following inline-only tree and point-lookup proofs are retained as
historical proof text. `decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow`
below replaces the former tree inverse on the live representation.

/-- Compositional raw inverse for the physical table tree.  Starting at the
encoded root and following the child pointers in the actual SQLite page bytes
recovers exactly the logical rows in the proof-carrying tree. -/
theorem decodeSubtreeRowsFrom_encodeChunkNode (schema : Core.Schema)
    (source : CoreDecode.PageSource) :
    ∀ (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
      (pages : List NumberedPage) (fuel : Nat),
      encodeChunkNode schema node = some pages →
      PageSourceContains source pages →
      node.erase.RootValid →
      (∀ entry ∈ node.erase.toList, ∀ row ∈ entry.2,
        row.WellFormed schema) →
      node.erase.height < fuel →
      CoreDecode.decodeSubtreeRowsFrom schema source fuel node.rootId =
        some (CoreChunkPageState.Node.rows node)
  | .leaf pageId entries, pages, fuel, encoded, contains, _, valid, enough => by
      simp only [encodeChunkNode] at encoded
      cases pageResult : encodeChunkLeaf schema entries with
      | none => simp [pageResult] at encoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at encoded
          subst pages
          cases fuel with
          | zero => simp [PersistentPageTree.Node.erase,
              RecursiveBPlusTree.Node.height] at enough
          | succ childFuel =>
              unfold CoreDecode.decodeSubtreeRowsFrom
              simp only [PersistentPageTree.Node.rootId]
              rw [contains ⟨pageId, page⟩ (by simp)]
              dsimp
              rw [interiorChildren_encodeChunkLeaf schema entries page pageResult]
              rw [decodeRowsFrom_encodeChunkLeaf schema entries page
                (fun entry member row rowMember =>
                  valid entry (by simpa using member) row rowMember)
                pageResult source]
              rfl
  | .branch2 pageId left separator right, pages, fuel, encoded, contains,
      rootValid, valid, enough => by
      simp only [encodeChunkNode] at encoded
      cases keyResult : maximumChunkRowid? left with
      | none => simp [keyResult] at encoded
      | some key =>
          simp only [keyResult, Option.bind_eq_bind, Option.bind] at encoded
          cases rootResult : RecursivePageBTree.interiorPage?
              [(left.rootId, key)] right.rootId with
          | none => simp [rootResult] at encoded
          | some root =>
              simp only [rootResult] at encoded
              cases leftResult : encodeChunkNode schema left with
              | none => simp [leftResult] at encoded
              | some leftPages =>
                  simp only [leftResult] at encoded
                  cases rightResult : encodeChunkNode schema right with
                  | none => simp [rightResult] at encoded
                  | some rightPages =>
                      simp only [rightResult, Option.some.injEq] at encoded
                      subst pages
                      cases fuel with
                      | zero => simp [PersistentPageTree.Node.erase,
                          RecursiveBPlusTree.Node.height] at enough
                      | succ childFuel =>
                          have rootRead : source.readPage pageId =
                              some root.bytes :=
                            contains ⟨pageId, root⟩ (by simp)
                          have leftContains :
                              PageSourceContains source leftPages := by
                            intro numbered member
                            exact contains numbered (by simp [member])
                          have rightContains :
                              PageSourceContains source rightPages := by
                            intro numbered member
                            exact contains numbered (by simp [member])
                          rcases rootValid with
                            ⟨leftValid, rightValid, heights, _, _⟩
                          have leftRowsValid : ∀ entry ∈ left.erase.toList,
                              ∀ row ∈ entry.2, row.WellFormed schema := by
                            intro entry member row rowMember
                            exact valid entry (by
                              simp only [PersistentPageTree.Node.erase,
                                RecursiveBPlusTree.Node.toList,
                                List.mem_append]
                              exact Or.inl member) row rowMember
                          have rightRowsValid : ∀ entry ∈ right.erase.toList,
                              ∀ row ∈ entry.2, row.WellFormed schema := by
                            intro entry member row rowMember
                            exact valid entry (by
                              simp only [PersistentPageTree.Node.erase,
                                RecursiveBPlusTree.Node.toList,
                                List.mem_append]
                              exact Or.inr member) row rowMember
                          have leftDecoded :=
                            decodeSubtreeRowsFrom_encodeChunkNode schema source
                              left leftPages childFuel leftResult leftContains
                              leftValid.rootValid leftRowsValid (by
                                simp [PersistentPageTree.Node.erase,
                                  RecursiveBPlusTree.Node.height] at enough
                                omega)
                          have rightDecoded :=
                            decodeSubtreeRowsFrom_encodeChunkNode schema source
                              right rightPages childFuel rightResult rightContains
                              rightValid.rootValid rightRowsValid (by
                                simp [PersistentPageTree.Node.erase,
                                  RecursiveBPlusTree.Node.height] at enough
                                omega)
                          unfold CoreDecode.decodeSubtreeRowsFrom
                          simp only [PersistentPageTree.Node.rootId]
                          rw [rootRead]
                          simp only [Option.bind_eq_bind, Option.bind]
                          rw [interiorChildren_interiorPage_one rootResult]
                          simp [leftDecoded, rightDecoded,
                            CoreChunkPageState.Node.rows,
                            PersistentPageTree.Node.erase,
                            RecursiveBPlusTree.Node.toList]
  | .branch3 pageId left firstSeparator middle secondSeparator right,
      pages, fuel, encoded, contains, rootValid, valid, enough => by
      simp only [encodeChunkNode] at encoded
      cases leftKeyResult : maximumChunkRowid? left with
      | none => simp [leftKeyResult] at encoded
      | some leftKey =>
          simp only [leftKeyResult, Option.bind_eq_bind, Option.bind] at encoded
          cases middleKeyResult : maximumChunkRowid? middle with
          | none => simp [middleKeyResult] at encoded
          | some middleKey =>
              simp only [middleKeyResult] at encoded
              cases rootResult : RecursivePageBTree.interiorPage?
                  [(left.rootId, leftKey), (middle.rootId, middleKey)]
                    right.rootId with
              | none => simp [rootResult] at encoded
              | some root =>
                  simp only [rootResult] at encoded
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
                              cases fuel with
                              | zero => simp [PersistentPageTree.Node.erase,
                                  RecursiveBPlusTree.Node.height] at enough
                              | succ childFuel =>
                                  have rootRead : source.readPage pageId =
                                      some root.bytes :=
                                    contains ⟨pageId, root⟩ (by simp)
                                  have leftContains :
                                      PageSourceContains source leftPages := by
                                    intro numbered member
                                    exact contains numbered (by simp [member])
                                  have middleContains :
                                      PageSourceContains source middlePages := by
                                    intro numbered member
                                    exact contains numbered (by simp [member])
                                  have rightContains :
                                      PageSourceContains source rightPages := by
                                    intro numbered member
                                    exact contains numbered (by simp [member])
                                  rcases rootValid with
                                    ⟨leftValid, middleValid, rightValid,
                                      leftHeight, rightHeight, _, _, _, _⟩
                                  have leftRowsValid :
                                      ∀ entry ∈ left.erase.toList,
                                        ∀ row ∈ entry.2,
                                          row.WellFormed schema := by
                                    intro entry member row rowMember
                                    exact valid entry (by
                                      simp only [PersistentPageTree.Node.erase,
                                        RecursiveBPlusTree.Node.toList,
                                        List.mem_append]
                                      exact Or.inl (Or.inl member)) row rowMember
                                  have middleRowsValid :
                                      ∀ entry ∈ middle.erase.toList,
                                        ∀ row ∈ entry.2,
                                          row.WellFormed schema := by
                                    intro entry member row rowMember
                                    exact valid entry (by
                                      simp only [PersistentPageTree.Node.erase,
                                        RecursiveBPlusTree.Node.toList,
                                        List.mem_append]
                                      exact Or.inl (Or.inr member)) row rowMember
                                  have rightRowsValid :
                                      ∀ entry ∈ right.erase.toList,
                                        ∀ row ∈ entry.2,
                                          row.WellFormed schema := by
                                    intro entry member row rowMember
                                    exact valid entry (by
                                      simp only [PersistentPageTree.Node.erase,
                                        RecursiveBPlusTree.Node.toList,
                                        List.mem_append]
                                      exact Or.inr member) row rowMember
                                  have leftDecoded :=
                                    decodeSubtreeRowsFrom_encodeChunkNode schema
                                      source left leftPages childFuel leftResult
                                      leftContains
                                      leftValid.rootValid
                                      leftRowsValid (by
                                          simp [PersistentPageTree.Node.erase,
                                            RecursiveBPlusTree.Node.height]
                                              at enough
                                          omega)
                                  have middleDecoded :=
                                    decodeSubtreeRowsFrom_encodeChunkNode schema
                                      source middle middlePages childFuel
                                      middleResult middleContains
                                      middleValid.rootValid
                                      middleRowsValid (by
                                          simp [PersistentPageTree.Node.erase,
                                            RecursiveBPlusTree.Node.height]
                                              at enough
                                          omega)
                                  have rightDecoded :=
                                    decodeSubtreeRowsFrom_encodeChunkNode schema
                                      source right rightPages childFuel rightResult
                                      rightContains
                                      rightValid.rootValid
                                      rightRowsValid (by
                                          simp [PersistentPageTree.Node.erase,
                                            RecursiveBPlusTree.Node.height]
                                              at enough
                                          omega)
                                  unfold CoreDecode.decodeSubtreeRowsFrom
                                  simp only [PersistentPageTree.Node.rootId]
                                  rw [rootRead]
                                  simp only [Option.bind_eq_bind, Option.bind]
                                  rw [interiorChildren_interiorPage_two rootResult]
                                  simp [leftDecoded, middleDecoded, rightDecoded,
                                    CoreChunkPageState.Node.rows,
                                    PersistentPageTree.Node.erase,
                                    RecursiveBPlusTree.Node.toList]

/-- Exact raw-page point lookup for every table tree emitted by the persistent
encoder.  It covers successful hits and valid misses: the result is precisely
the rowid search of the tree abstraction, while acquiring one child per level. -/
theorem lookupTableRowidFrom_encodeChunkNode (schema : Core.Schema)
    (source : CoreDecode.PageSource) (target : Core.Integer) :
    ∀ (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
      (pages : List NumberedPage) (fuel : Nat),
      encodeChunkNode schema node = some pages →
      PageSourceContains source pages →
      node.erase.RootValid →
      (∀ entry ∈ node.erase.toList, ∀ row ∈ entry.2,
        row.WellFormed schema) →
      (∀ pageId ∈ node.pageIds, 0 < pageId) →
      (CoreChunkPageState.Node.rows node).Pairwise Core.Row.keyLess →
      node.erase.height < fuel →
      CoreDecode.lookupTableRowidFrom schema source target fuel node.rootId =
        some ((CoreChunkPageState.Node.rows node).find?
          fun row => row.rowid = target)
  | .leaf pageId entries, pages, fuel, encoded, contains, _, valid, _, _,
      enough => by
      simp only [encodeChunkNode] at encoded
      cases pageResult : encodeChunkLeaf schema entries with
      | none => simp [pageResult] at encoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at encoded
          subst pages
          cases fuel with
          | zero => simp [PersistentPageTree.Node.erase,
              RecursiveBPlusTree.Node.height] at enough
          | succ childFuel =>
              rw [CoreDecode.lookupTableRowidFrom_succ]
              simp only [PersistentPageTree.Node.rootId]
              rw [contains ⟨pageId, page⟩ (by simp)]
              simp only [decodeTableInterior_encodeChunkLeaf schema entries
                page pageResult]
              rw [decodeRowsFrom_encodeChunkLeaf schema entries page
                (fun entry member row rowMember =>
                  valid entry (by simpa using member) row rowMember)
                pageResult source]
              rfl
  | .branch2 pageId left separator right, pages, fuel, encoded, contains,
      rootValid, valid, positive, ordered, enough => by
      simp only [encodeChunkNode] at encoded
      cases keyResult : maximumChunkRowid? left with
      | none => simp [keyResult] at encoded
      | some key =>
          simp only [keyResult, Option.bind_eq_bind, Option.bind] at encoded
          cases rootResult : RecursivePageBTree.interiorPage?
              [(left.rootId, key)] right.rootId with
          | none => simp [rootResult] at encoded
          | some root =>
              simp only [rootResult] at encoded
              cases leftResult : encodeChunkNode schema left with
              | none => simp [leftResult] at encoded
              | some leftPages =>
                  simp only [leftResult] at encoded
                  cases rightResult : encodeChunkNode schema right with
                  | none => simp [rightResult] at encoded
                  | some rightPages =>
                      simp only [rightResult, Option.some.injEq] at encoded
                      subst pages
                      cases fuel with
                      | zero => simp [PersistentPageTree.Node.erase,
                          RecursiveBPlusTree.Node.height] at enough
                      | succ childFuel =>
                          have rootRead : source.readPage pageId =
                              some root.bytes :=
                            contains ⟨pageId, root⟩ (by simp)
                          have leftContains :
                              PageSourceContains source leftPages := by
                            intro numbered member
                            exact contains numbered (by simp [member])
                          have rightContains :
                              PageSourceContains source rightPages := by
                            intro numbered member
                            exact contains numbered (by simp [member])
                          rcases rootValid with
                            ⟨leftValid, rightValid, heights, _, _⟩
                          have leftRowsValid : ∀ entry ∈ left.erase.toList,
                              ∀ row ∈ entry.2, row.WellFormed schema := by
                            intro entry member row rowMember
                            exact valid entry (by
                              simp only [PersistentPageTree.Node.erase,
                                RecursiveBPlusTree.Node.toList,
                                List.mem_append]
                              exact Or.inl member) row rowMember
                          have rightRowsValid : ∀ entry ∈ right.erase.toList,
                              ∀ row ∈ entry.2, row.WellFormed schema := by
                            intro entry member row rowMember
                            exact valid entry (by
                              simp only [PersistentPageTree.Node.erase,
                                RecursiveBPlusTree.Node.toList,
                                List.mem_append]
                              exact Or.inr member) row rowMember
                          have leftPositive : ∀ id ∈ left.pageIds, 0 < id := by
                            intro id member
                            apply positive id
                            simp only [PersistentPageTree.Node.pageIds,
                              List.mem_cons, List.mem_append]
                            exact Or.inl (Or.inr member)
                          have rightPositive : ∀ id ∈ right.pageIds, 0 < id := by
                            intro id member
                            apply positive id
                            simp only [PersistentPageTree.Node.pageIds,
                              List.mem_cons, List.mem_append]
                            exact Or.inr member
                          have childrenOrdered :
                              (CoreChunkPageState.Node.rows left ++
                                CoreChunkPageState.Node.rows right).Pairwise
                                  Core.Row.keyLess := by
                            simpa [CoreChunkPageState.Node.rows,
                              PersistentPageTree.Node.erase,
                              RecursiveBPlusTree.Node.toList,
                              List.flatMap_append] using ordered
                          have leftLookup :=
                            lookupTableRowidFrom_encodeChunkNode schema source
                              target left leftPages childFuel leftResult
                              leftContains leftValid.rootValid leftRowsValid
                              leftPositive
                              (List.pairwise_append.mp childrenOrdered).1 (by
                                simp [PersistentPageTree.Node.erase,
                                  RecursiveBPlusTree.Node.height] at enough
                                omega)
                          have rightLookup :=
                            lookupTableRowidFrom_encodeChunkNode schema source
                              target right rightPages childFuel rightResult
                              rightContains rightValid.rootValid rightRowsValid
                              rightPositive
                              (List.pairwise_append.mp childrenOrdered).2.1 (by
                                simp [PersistentPageTree.Node.erase,
                                  RecursiveBPlusTree.Node.height] at enough
                                omega)
                          rcases maximumChunkRowid?_witness keyResult with
                            ⟨boundary, boundaryLast, rfl⟩
                          have keyBound : boundary.rowid.toUnsigned < 2 ^ 64 := by
                            simpa [FileFormat.IntegerWidth.modulus] using
                              boundary.rowid.toUnsigned_lt
                          have leftRootPositive : 0 < left.rootId :=
                            leftPositive left.rootId left.rootId_mem_pageIds
                          have routing := findRowid_append_routed target
                            boundary.rowid
                            (CoreChunkPageState.Node.rows left)
                            (CoreChunkPageState.Node.rows right)
                            childrenOrdered (by rw [boundaryLast]; rfl)
                          rw [CoreDecode.lookupTableRowidFrom_succ]
                          simp only [PersistentPageTree.Node.rootId]
                          rw [rootRead]
                          simp only [decodeTableInterior_interiorPage_one
                            leftRootPositive keyBound rootResult]
                          rw [FileFormat.signedIntegerFromUnsigned_toUnsigned]
                          by_cases routed :
                              target.value ≤ boundary.rowid.value
                          · have findEqual : findRowid target
                                (CoreChunkPageState.Node.rows left ++
                                  CoreChunkPageState.Node.rows right) =
                                findRowid target
                                  (CoreChunkPageState.Node.rows left) := by
                              simpa [routed] using routing
                            simpa [CoreDecode.tableChildForRowid, routed,
                              leftLookup, findRowid,
                              CoreChunkPageState.Node.rows,
                              PersistentPageTree.Node.erase,
                              RecursiveBPlusTree.Node.toList,
                              List.flatMap_append] using congrArg some
                                findEqual.symm
                          · have findEqual : findRowid target
                                (CoreChunkPageState.Node.rows left ++
                                  CoreChunkPageState.Node.rows right) =
                                findRowid target
                                  (CoreChunkPageState.Node.rows right) := by
                              simpa [routed] using routing
                            simpa [CoreDecode.tableChildForRowid, routed,
                              rightLookup, findRowid,
                              CoreChunkPageState.Node.rows,
                              PersistentPageTree.Node.erase,
                              RecursiveBPlusTree.Node.toList,
                              List.flatMap_append] using congrArg some
                                findEqual.symm
  | .branch3 pageId left firstSeparator middle secondSeparator right, pages,
      fuel, encoded, contains, rootValid, valid, positive, ordered, enough => by
      simp only [encodeChunkNode] at encoded
      cases leftKeyResult : maximumChunkRowid? left with
      | none => simp [leftKeyResult] at encoded
      | some leftKey =>
          simp only [leftKeyResult, Option.bind_eq_bind, Option.bind] at encoded
          cases middleKeyResult : maximumChunkRowid? middle with
          | none => simp [middleKeyResult] at encoded
          | some middleKey =>
              simp only [middleKeyResult] at encoded
              cases rootResult : RecursivePageBTree.interiorPage?
                  [(left.rootId, leftKey), (middle.rootId, middleKey)]
                    right.rootId with
              | none => simp [rootResult] at encoded
              | some root =>
                  simp only [rootResult] at encoded
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
                              cases fuel with
                              | zero => simp [PersistentPageTree.Node.erase,
                                  RecursiveBPlusTree.Node.height] at enough
                              | succ childFuel =>
                                  have rootRead : source.readPage pageId =
                                      some root.bytes :=
                                    contains ⟨pageId, root⟩ (by simp)
                                  have leftContains : PageSourceContains source
                                      leftPages := by
                                    intro numbered member
                                    exact contains numbered (by simp [member])
                                  have middleContains : PageSourceContains source
                                      middlePages := by
                                    intro numbered member
                                    exact contains numbered (by simp [member])
                                  have rightContains : PageSourceContains source
                                      rightPages := by
                                    intro numbered member
                                    exact contains numbered (by simp [member])
                                  rcases rootValid with
                                    ⟨leftValid, middleValid, rightValid,
                                      leftHeight, rightHeight, _, _, _, _⟩
                                  have leftRowsValid : ∀ entry ∈ left.erase.toList,
                                      ∀ row ∈ entry.2, row.WellFormed schema := by
                                    intro entry member row rowMember
                                    exact valid entry (by
                                      simp only [PersistentPageTree.Node.erase,
                                        RecursiveBPlusTree.Node.toList,
                                        List.mem_append]
                                      exact Or.inl (Or.inl member)) row rowMember
                                  have middleRowsValid :
                                      ∀ entry ∈ middle.erase.toList,
                                        ∀ row ∈ entry.2,
                                          row.WellFormed schema := by
                                    intro entry member row rowMember
                                    exact valid entry (by
                                      simp only [PersistentPageTree.Node.erase,
                                        RecursiveBPlusTree.Node.toList,
                                        List.mem_append]
                                      exact Or.inl (Or.inr member)) row rowMember
                                  have rightRowsValid :
                                      ∀ entry ∈ right.erase.toList,
                                        ∀ row ∈ entry.2,
                                          row.WellFormed schema := by
                                    intro entry member row rowMember
                                    exact valid entry (by
                                      simp only [PersistentPageTree.Node.erase,
                                        RecursiveBPlusTree.Node.toList,
                                        List.mem_append]
                                      exact Or.inr member) row rowMember
                                  have leftPositive :
                                      ∀ id ∈ left.pageIds, 0 < id := by
                                    intro id member
                                    apply positive id
                                    simp only [PersistentPageTree.Node.pageIds,
                                      List.mem_cons, List.mem_append]
                                    exact Or.inl (Or.inl (Or.inr member))
                                  have middlePositive :
                                      ∀ id ∈ middle.pageIds, 0 < id := by
                                    intro id member
                                    apply positive id
                                    simp only [PersistentPageTree.Node.pageIds,
                                      List.mem_cons, List.mem_append]
                                    exact Or.inl (Or.inr member)
                                  have rightPositive :
                                      ∀ id ∈ right.pageIds, 0 < id := by
                                    intro id member
                                    apply positive id
                                    simp only [PersistentPageTree.Node.pageIds,
                                      List.mem_cons, List.mem_append]
                                    exact Or.inr member
                                  have childrenOrdered :
                                      (CoreChunkPageState.Node.rows left ++
                                        CoreChunkPageState.Node.rows middle ++
                                        CoreChunkPageState.Node.rows right).Pairwise
                                          Core.Row.keyLess := by
                                    simpa [CoreChunkPageState.Node.rows,
                                      PersistentPageTree.Node.erase,
                                      RecursiveBPlusTree.Node.toList,
                                      List.flatMap_append,
                                      List.append_assoc] using ordered
                                  have firstSplit :=
                                    List.pairwise_append.mp (show
                                      (CoreChunkPageState.Node.rows left ++
                                        (CoreChunkPageState.Node.rows middle ++
                                          CoreChunkPageState.Node.rows right)).Pairwise
                                            Core.Row.keyLess from by
                                        simpa only [List.append_assoc] using
                                          childrenOrdered)
                                  have middleRightOrdered :
                                      (CoreChunkPageState.Node.rows middle ++
                                        CoreChunkPageState.Node.rows right).Pairwise
                                          Core.Row.keyLess := by
                                    exact firstSplit.2.1
                                  have secondSplit :=
                                    List.pairwise_append.mp middleRightOrdered
                                  have leftLookup :=
                                    lookupTableRowidFrom_encodeChunkNode schema
                                      source target left leftPages childFuel
                                      leftResult leftContains
                                      leftValid.rootValid leftRowsValid
                                      leftPositive firstSplit.1 (by
                                        simp [PersistentPageTree.Node.erase,
                                          RecursiveBPlusTree.Node.height] at enough
                                        omega)
                                  have middleLookup :=
                                    lookupTableRowidFrom_encodeChunkNode schema
                                      source target middle middlePages childFuel
                                      middleResult middleContains
                                      middleValid.rootValid middleRowsValid
                                      middlePositive secondSplit.1 (by
                                        simp [PersistentPageTree.Node.erase,
                                          RecursiveBPlusTree.Node.height] at enough
                                        omega)
                                  have rightLookup :=
                                    lookupTableRowidFrom_encodeChunkNode schema
                                      source target right rightPages childFuel
                                      rightResult rightContains
                                      rightValid.rootValid rightRowsValid
                                      rightPositive secondSplit.2.1 (by
                                        simp [PersistentPageTree.Node.erase,
                                          RecursiveBPlusTree.Node.height] at enough
                                        omega)
                                  rcases maximumChunkRowid?_witness leftKeyResult
                                    with ⟨leftBoundary, leftLast, rfl⟩
                                  rcases maximumChunkRowid?_witness middleKeyResult
                                    with ⟨middleBoundary, middleLast, rfl⟩
                                  have leftKeyBound :
                                      leftBoundary.rowid.toUnsigned < 2 ^ 64 := by
                                    simpa [FileFormat.IntegerWidth.modulus] using
                                      leftBoundary.rowid.toUnsigned_lt
                                  have middleKeyBound :
                                      middleBoundary.rowid.toUnsigned < 2 ^ 64 := by
                                    simpa [FileFormat.IntegerWidth.modulus] using
                                      middleBoundary.rowid.toUnsigned_lt
                                  have leftRootPositive : 0 < left.rootId :=
                                    leftPositive left.rootId
                                      left.rootId_mem_pageIds
                                  have middleRootPositive : 0 < middle.rootId :=
                                    middlePositive middle.rootId
                                      middle.rootId_mem_pageIds
                                  have firstRouting := findRowid_append_routed
                                    target leftBoundary.rowid
                                    (CoreChunkPageState.Node.rows left)
                                    (CoreChunkPageState.Node.rows middle ++
                                      CoreChunkPageState.Node.rows right)
                                    (show (CoreChunkPageState.Node.rows left ++
                                      (CoreChunkPageState.Node.rows middle ++
                                        CoreChunkPageState.Node.rows right)).Pairwise
                                          Core.Row.keyLess from by
                                      simpa only [List.append_assoc] using
                                        childrenOrdered)
                                    (by rw [leftLast]; rfl)
                                  have secondRouting := findRowid_append_routed
                                    target middleBoundary.rowid
                                    (CoreChunkPageState.Node.rows middle)
                                    (CoreChunkPageState.Node.rows right)
                                    middleRightOrdered (by rw [middleLast]; rfl)
                                  rw [CoreDecode.lookupTableRowidFrom_succ]
                                  simp only [PersistentPageTree.Node.rootId]
                                  rw [rootRead]
                                  simp only [decodeTableInterior_interiorPage_two
                                    leftRootPositive middleRootPositive
                                    leftKeyBound middleKeyBound rootResult]
                                  simp only [FileFormat.signedIntegerFromUnsigned_toUnsigned]
                                  by_cases leftRoute :
                                      target.value ≤ leftBoundary.rowid.value
                                  · have findEqual : findRowid target
                                        (CoreChunkPageState.Node.rows left ++
                                          CoreChunkPageState.Node.rows middle ++
                                          CoreChunkPageState.Node.rows right) =
                                        findRowid target
                                          (CoreChunkPageState.Node.rows left) := by
                                      simpa [leftRoute, List.append_assoc] using
                                        firstRouting
                                    simpa [CoreDecode.tableChildForRowid,
                                      leftRoute, leftLookup, findRowid,
                                      CoreChunkPageState.Node.rows,
                                      PersistentPageTree.Node.erase,
                                      RecursiveBPlusTree.Node.toList,
                                      List.flatMap_append,
                                      List.append_assoc] using congrArg some
                                        findEqual.symm
                                  · by_cases middleRoute :
                                        target.value ≤ middleBoundary.rowid.value
                                    · have firstEqual : findRowid target
                                          (CoreChunkPageState.Node.rows left ++
                                            (CoreChunkPageState.Node.rows middle ++
                                              CoreChunkPageState.Node.rows right)) =
                                          findRowid target
                                            (CoreChunkPageState.Node.rows middle ++
                                              CoreChunkPageState.Node.rows right) := by
                                        simpa [leftRoute] using firstRouting
                                      have secondEqual : findRowid target
                                          (CoreChunkPageState.Node.rows middle ++
                                            CoreChunkPageState.Node.rows right) =
                                          findRowid target
                                            (CoreChunkPageState.Node.rows middle) := by
                                        simpa [middleRoute] using secondRouting
                                      have findEqual := firstEqual.trans secondEqual
                                      simpa [CoreDecode.tableChildForRowid,
                                        leftRoute, middleRoute, middleLookup,
                                        findRowid, CoreChunkPageState.Node.rows,
                                        PersistentPageTree.Node.erase,
                                        RecursiveBPlusTree.Node.toList,
                                        List.flatMap_append,
                                        List.append_assoc] using congrArg some
                                          findEqual.symm
                                    · have firstEqual : findRowid target
                                          (CoreChunkPageState.Node.rows left ++
                                            (CoreChunkPageState.Node.rows middle ++
                                              CoreChunkPageState.Node.rows right)) =
                                          findRowid target
                                            (CoreChunkPageState.Node.rows middle ++
                                              CoreChunkPageState.Node.rows right) := by
                                        simpa [leftRoute] using firstRouting
                                      have secondEqual : findRowid target
                                          (CoreChunkPageState.Node.rows middle ++
                                            CoreChunkPageState.Node.rows right) =
                                          findRowid target
                                            (CoreChunkPageState.Node.rows right) := by
                                        simpa [middleRoute] using secondRouting
                                      have findEqual := firstEqual.trans secondEqual
                                      simpa [CoreDecode.tableChildForRowid,
                                        leftRoute, middleRoute, rightLookup,
                                        findRowid, CoreChunkPageState.Node.rows,
                                        PersistentPageTree.Node.erase,
                                        RecursiveBPlusTree.Node.toList,
                                        List.flatMap_append,
                                        List.append_assoc] using congrArg some
                                          findEqual.symm
-/

theorem interiorChildren_encodeChunkRoot_branch2 (schema : Core.Schema)
    (pageId : Nat) (left : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (separator : Nat)
    (right : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (root : NumberedPage)
    (built : encodeChunkRoot schema
      (.branch2 pageId left separator right) = some root) :
    CoreDecode.interiorChildren? root.page.bytes =
      some [left.rootId, right.rootId] := by
  simp only [encodeChunkRoot] at built
  cases keyResult : maximumChunkRowid? left with
  | none => simp [keyResult] at built
  | some key =>
    simp only [keyResult, Option.bind_eq_bind, Option.bind] at built
    cases pageResult : RecursivePageBTree.interiorPage?
        [(left.rootId, key)] right.rootId with
    | none => simp [pageResult] at built
    | some page =>
      simp only [pageResult, Option.some.injEq] at built
      subst root
      exact interiorChildren_interiorPage_one pageResult

theorem interiorChildren_encodeChunkRoot_branch3 (schema : Core.Schema)
    (pageId : Nat) (left : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (firstSeparator : Nat)
    (middle : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (secondSeparator : Nat)
    (right : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (root : NumberedPage)
    (built : encodeChunkRoot schema
      (.branch3 pageId left firstSeparator middle secondSeparator right) =
        some root) :
    CoreDecode.interiorChildren? root.page.bytes =
      some [left.rootId, middle.rootId, right.rootId] := by
  simp only [encodeChunkRoot] at built
  cases leftResult : maximumChunkRowid? left with
  | none => simp [leftResult] at built
  | some leftKey =>
    simp only [leftResult, Option.bind_eq_bind, Option.bind] at built
    cases middleResult : maximumChunkRowid? middle with
    | none => simp [middleResult] at built
    | some middleKey =>
      simp only [middleResult] at built
      cases pageResult : RecursivePageBTree.interiorPage?
          [(left.rootId, leftKey), (middle.rootId, middleKey)] right.rootId with
      | none => simp [pageResult] at built
      | some page =>
        simp only [pageResult, Option.some.injEq] at built
        subst root
        exact interiorChildren_interiorPage_two pageResult

def encodeChunkPath (schema : Core.Schema) (key : Nat) :
    PersistentPageTree.Node CoreChunkPageState.Chunk →
      Option (List NumberedPage)
  | node@(.leaf ..) => do
      let page ← encodeChunkRoot schema node
      some [page]
  | node@(.branch2 _ left separator right) => do
      let page ← encodeChunkRoot schema node
      let child ← if key < separator then encodeChunkPath schema key left
        else encodeChunkPath schema key right
      some (page :: child)
  | node@(.branch3 _ left firstSeparator middle secondSeparator right) => do
      let page ← encodeChunkRoot schema node
      let child ← if key < firstSeparator then encodeChunkPath schema key left
        else if key < secondSeparator then encodeChunkPath schema key middle
        else encodeChunkPath schema key right
      some (page :: child)

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

def encodeChunkTablesWithOverflow : Nat →
    List CoreChunkPageState.TableState → Option OverflowEncoding
  | nextOverflow, [] => some ⟨[], [], nextOverflow⟩
  | nextOverflow, table :: tables => do
      let head ← encodeChunkNodeWithOverflow table.table.schema table.tree.root
        nextOverflow
      let tail ← encodeChunkTablesWithOverflow head.nextPage tables
      some {
        treePages := head.treePages ++ tail.treePages
        overflowPages := head.overflowPages ++ tail.overflowPages
        nextPage := tail.nextPage }

theorem encodeChunkNodeWithOverflow_pageNumbers (schema : Core.Schema)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (nextOverflow : Nat) (encoding : OverflowEncoding)
    (encoded : encodeChunkNodeWithOverflow schema node nextOverflow =
      some encoding) :
    encoding.treePages.map NumberedPage.pageNumber = node.pageIds := by
  induction node generalizing nextOverflow encoding with
  | leaf pageId entries =>
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases plansResult :
          (entries.flatMap fun entry => entry.2).mapM
            (CoreOverflow.tableCellPlan? schema) with
      | none => simp [plansResult] at encoded
      | some plans =>
          simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
          cases resolvedResult : CoreOverflow.resolvePlans nextOverflow plans with
          | none => simp [resolvedResult] at encoded
          | some resolved =>
              simp only [resolvedResult] at encoded
              cases pageResult : CoreFile.tableLeafPage? resolved.cells with
              | none => simp [pageResult] at encoded
              | some page =>
                  simp only [pageResult, Option.some.injEq] at encoded
                  subst encoding
                  rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch2 pageId left separator right) with
      | none => simp [rootResult] at encoded
      | some root =>
          simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
          cases leftResult : encodeChunkNodeWithOverflow schema left
              nextOverflow with
          | none => simp [leftResult] at encoded
          | some leftEncoding =>
              simp only [leftResult] at encoded
              cases rightResult : encodeChunkNodeWithOverflow schema right
                  leftEncoding.nextPage with
              | none => simp [rightResult] at encoded
              | some rightEncoding =>
                  simp only [rightResult, Option.some.injEq] at encoded
                  subst encoding
                  simp only [List.map_cons, List.map_append,
                    PersistentPageTree.Node.pageIds]
                  rw [encodeChunkRoot_pageNumber schema _ root rootResult,
                    leftInduction nextOverflow leftEncoding leftResult,
                    rightInduction leftEncoding.nextPage rightEncoding
                      rightResult]
                  rfl
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch3 pageId left firstSeparator middle secondSeparator right) with
      | none => simp [rootResult] at encoded
      | some root =>
          simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
          cases leftResult : encodeChunkNodeWithOverflow schema left
              nextOverflow with
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
                      simp only [List.map_cons, List.map_append,
                        PersistentPageTree.Node.pageIds]
                      rw [encodeChunkRoot_pageNumber schema _ root rootResult,
                        leftInduction nextOverflow leftEncoding leftResult,
                        middleInduction leftEncoding.nextPage middleEncoding
                          middleResult,
                        rightInduction middleEncoding.nextPage rightEncoding
                          rightResult]
                      rfl

theorem encodeChunkNodeWithOverflow_nextPage (schema : Core.Schema)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (nextOverflow : Nat) (encoding : OverflowEncoding)
    (encoded : encodeChunkNodeWithOverflow schema node nextOverflow =
      some encoding) :
    encoding.nextPage = nextOverflow + encoding.overflowPages.length := by
  induction node generalizing nextOverflow encoding with
  | leaf pageId entries =>
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases plansResult :
          (entries.flatMap fun entry => entry.2).mapM
            (CoreOverflow.tableCellPlan? schema) with
      | none => simp [plansResult] at encoded
      | some plans =>
          simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
          cases resolvedResult : CoreOverflow.resolvePlans nextOverflow plans with
          | none => simp [resolvedResult] at encoded
          | some resolved =>
              simp only [resolvedResult] at encoded
              cases pageResult : CoreFile.tableLeafPage? resolved.cells with
              | none => simp [pageResult] at encoded
              | some page =>
                  simp only [pageResult, Option.some.injEq] at encoded
                  subst encoding
                  exact CoreOverflow.resolvePlans_nextPage resolvedResult
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch2 pageId left separator right) with
      | none => simp [rootResult] at encoded
      | some root =>
          simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
          cases leftResult : encodeChunkNodeWithOverflow schema left
              nextOverflow with
          | none => simp [leftResult] at encoded
          | some leftEncoding =>
              simp only [leftResult] at encoded
              cases rightResult : encodeChunkNodeWithOverflow schema right
                  leftEncoding.nextPage with
              | none => simp [rightResult] at encoded
              | some rightEncoding =>
                  simp only [rightResult, Option.some.injEq] at encoded
                  subst encoding
                  simp only [List.length_append]
                  rw [rightInduction leftEncoding.nextPage rightEncoding
                    rightResult,
                    leftInduction nextOverflow leftEncoding leftResult]
                  omega
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch3 pageId left firstSeparator middle secondSeparator right) with
      | none => simp [rootResult] at encoded
      | some root =>
          simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
          cases leftResult : encodeChunkNodeWithOverflow schema left
              nextOverflow with
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
                      simp only [List.length_append]
                      rw [rightInduction middleEncoding.nextPage rightEncoding
                        rightResult,
                        middleInduction leftEncoding.nextPage middleEncoding
                          middleResult,
                        leftInduction nextOverflow leftEncoding leftResult]
                      omega

/-- Full raw-page inverse for the store-owned tree with overflow payloads.
Tree pages are addressed by persistent identities; the separately allocated
overflow interval is split compositionally between recursive children. -/
theorem decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow
    (schema : Core.Schema) (source : CoreDecode.PageSource) :
    ∀ (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
      (nextOverflow : Nat) (encoding : OverflowEncoding) (fuel : Nat),
      encodeChunkNodeWithOverflow schema node nextOverflow = some encoding →
      PageSourceContains source encoding.treePages →
      CoreDecode.ReadsPagesFrom source nextOverflow encoding.overflowPages →
      node.erase.RootValid →
      (∀ entry ∈ node.erase.toList, ∀ row ∈ entry.2,
        row.WellFormed schema) →
      node.erase.height < fuel →
      0 < nextOverflow →
      nextOverflow + encoding.overflowPages.length < 2 ^ 32 →
      encoding.overflowPages.length < source.pageCount + 1 →
      CoreDecode.decodeSubtreeRowsFrom schema source fuel node.rootId =
        some (CoreChunkPageState.Node.rows node)
  | .leaf pageId entries, nextOverflow, encoding, fuel, encoded, treeContains,
      overflowContains, _, valid, enough, nextPositive, pageBound, fuelBound => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases plansResult :
          (entries.flatMap fun entry => entry.2).mapM
            (CoreOverflow.tableCellPlan? schema) with
      | none => simp [plansResult] at encoded
      | some plans =>
        simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
        cases resolvedResult : CoreOverflow.resolvePlans nextOverflow plans with
        | none => simp [resolvedResult] at encoded
        | some resolved =>
          simp only [resolvedResult] at encoded
          cases pageResult : CoreFile.tableLeafPage? resolved.cells with
          | none => simp [pageResult] at encoded
          | some page =>
            simp only [pageResult, Option.some.injEq] at encoded
            subst encoding
            cases fuel with
            | zero =>
              simp [PersistentPageTree.Node.erase,
                RecursiveBPlusTree.Node.height] at enough
            | succ childFuel =>
              let rows := entries.flatMap fun entry => entry.2
              have rowsValid : ∀ row ∈ rows, row.WellFormed schema := by
                intro row member
                simp only [rows, List.mem_flatMap] at member
                rcases member with ⟨entry, entryMember, rowMember⟩
                exact valid entry (by simpa [PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList] using entryMember) row rowMember
              have rootRead : source.readPage pageId = some page.bytes :=
                treeContains ⟨pageId, page⟩ (by simp)
              have decoded := CoreDecode.decodeRowsFrom_resolvedLeaf schema source
                rows plans nextOverflow resolved page rowsValid
                (by simpa [rows] using plansResult) resolvedResult pageResult
                nextPositive (by simpa using pageBound)
                (by simpa using fuelBound) overflowContains
              unfold CoreDecode.decodeSubtreeRowsFrom
              simp only [PersistentPageTree.Node.rootId]
              rw [rootRead]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [interiorChildren_tableLeafPage pageResult, decoded]
              rfl
  | .branch2 pageId left separator right, nextOverflow, encoding, fuel,
      encoded, treeContains, overflowContains, rootValid, valid, enough,
      nextPositive, pageBound, fuelBound => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch2 pageId left separator right) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
        cases leftResult : encodeChunkNodeWithOverflow schema left
            nextOverflow with
        | none => simp [leftResult] at encoded
        | some leftEncoding =>
          simp only [leftResult] at encoded
          cases rightResult : encodeChunkNodeWithOverflow schema right
              leftEncoding.nextPage with
          | none => simp [rightResult] at encoded
          | some rightEncoding =>
            simp only [rightResult, Option.some.injEq] at encoded
            subst encoding
            cases fuel with
            | zero =>
              simp [PersistentPageTree.Node.erase,
                RecursiveBPlusTree.Node.height] at enough
            | succ childFuel =>
              have rootNumber := encodeChunkRoot_pageNumber schema
                (.branch2 pageId left separator right) root rootResult
              have rootNumber' : root.pageNumber = pageId := by
                simpa [PersistentPageTree.Node.rootId] using rootNumber
              have rootRead : source.readPage pageId = some root.page.bytes := by
                rw [← rootNumber']
                exact treeContains root (by simp)
              have leftTreeContains :
                  PageSourceContains source leftEncoding.treePages := by
                intro numbered member
                exact treeContains numbered (by simp [member])
              have rightTreeContains :
                  PageSourceContains source rightEncoding.treePages := by
                intro numbered member
                exact treeContains numbered (by simp [member])
              have leftOverflowContains : CoreDecode.ReadsPagesFrom source
                  nextOverflow leftEncoding.overflowPages :=
                CoreDecode.ReadsPagesFrom.left overflowContains
              have leftNext := encodeChunkNodeWithOverflow_nextPage schema left
                nextOverflow leftEncoding leftResult
              have rightOverflowContains : CoreDecode.ReadsPagesFrom source
                  leftEncoding.nextPage rightEncoding.overflowPages := by
                rw [leftNext]
                exact CoreDecode.ReadsPagesFrom.right overflowContains
              rcases rootValid with
                ⟨leftValid, rightValid, heights, _, _⟩
              have leftRowsValid : ∀ entry ∈ left.erase.toList,
                  ∀ row ∈ entry.2, row.WellFormed schema := by
                intro entry member row rowMember
                exact valid entry (by
                  simp only [PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.mem_append]
                  exact Or.inl member) row rowMember
              have rightRowsValid : ∀ entry ∈ right.erase.toList,
                  ∀ row ∈ entry.2, row.WellFormed schema := by
                intro entry member row rowMember
                exact valid entry (by
                  simp only [PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.mem_append]
                  exact Or.inr member) row rowMember
              have leftDecoded :=
                decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow schema source
                  left nextOverflow leftEncoding childFuel leftResult
                  leftTreeContains leftOverflowContains leftValid.rootValid
                  leftRowsValid (by
                    simp [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.height] at enough
                    omega)
                  nextPositive
                  (by simp only [List.length_append] at pageBound; omega)
                  (by simp only [List.length_append] at fuelBound; omega)
              have rightDecoded :=
                decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow schema source
                  right leftEncoding.nextPage rightEncoding childFuel rightResult
                  rightTreeContains rightOverflowContains rightValid.rootValid
                  rightRowsValid (by
                    simp [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.height] at enough
                    omega)
                  (by rw [leftNext]; omega)
                  (by
                    simp only [List.length_append] at pageBound
                    rw [leftNext]
                    omega)
                  (by simp only [List.length_append] at fuelBound; omega)
              unfold CoreDecode.decodeSubtreeRowsFrom
              simp only [PersistentPageTree.Node.rootId]
              rw [rootRead]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [interiorChildren_encodeChunkRoot_branch2 schema pageId left
                separator right root rootResult]
              simp [leftDecoded, rightDecoded, CoreChunkPageState.Node.rows,
                PersistentPageTree.Node.erase,
                RecursiveBPlusTree.Node.toList]
  | .branch3 pageId left firstSeparator middle secondSeparator right,
      nextOverflow, encoding, fuel, encoded, treeContains, overflowContains,
      rootValid, valid, enough, nextPositive, pageBound, fuelBound => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch3 pageId left firstSeparator middle secondSeparator right) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
        cases leftResult : encodeChunkNodeWithOverflow schema left
            nextOverflow with
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
              cases fuel with
              | zero =>
                simp [PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.height] at enough
              | succ childFuel =>
                change CoreDecode.ReadsPagesFrom source nextOverflow
                  (leftEncoding.overflowPages ++
                    middleEncoding.overflowPages ++
                    rightEncoding.overflowPages) at overflowContains
                have rootNumber := encodeChunkRoot_pageNumber schema
                  (.branch3 pageId left firstSeparator middle secondSeparator
                    right) root rootResult
                have rootNumber' : root.pageNumber = pageId := by
                  simpa [PersistentPageTree.Node.rootId] using rootNumber
                have rootRead : source.readPage pageId = some root.page.bytes := by
                  rw [← rootNumber']
                  exact treeContains root (by simp)
                have leftTreeContains :
                    PageSourceContains source leftEncoding.treePages := by
                  intro numbered member
                  exact treeContains numbered (by simp [member])
                have middleTreeContains :
                    PageSourceContains source middleEncoding.treePages := by
                  intro numbered member
                  exact treeContains numbered (by simp [member])
                have rightTreeContains :
                    PageSourceContains source rightEncoding.treePages := by
                  intro numbered member
                  exact treeContains numbered (by simp [member])
                rw [List.append_assoc] at overflowContains
                have leftOverflowContains : CoreDecode.ReadsPagesFrom source
                    nextOverflow leftEncoding.overflowPages :=
                  CoreDecode.ReadsPagesFrom.left overflowContains
                have leftNext := encodeChunkNodeWithOverflow_nextPage schema left
                  nextOverflow leftEncoding leftResult
                have afterLeft : CoreDecode.ReadsPagesFrom source
                    leftEncoding.nextPage
                    (middleEncoding.overflowPages ++
                      rightEncoding.overflowPages) := by
                  rw [leftNext]
                  exact CoreDecode.ReadsPagesFrom.right overflowContains
                have middleOverflowContains : CoreDecode.ReadsPagesFrom source
                    leftEncoding.nextPage middleEncoding.overflowPages :=
                  CoreDecode.ReadsPagesFrom.left afterLeft
                have middleNext := encodeChunkNodeWithOverflow_nextPage schema
                  middle leftEncoding.nextPage middleEncoding middleResult
                have rightOverflowContains : CoreDecode.ReadsPagesFrom source
                    middleEncoding.nextPage rightEncoding.overflowPages := by
                  rw [middleNext]
                  exact CoreDecode.ReadsPagesFrom.right afterLeft
                rcases rootValid with
                  ⟨leftValid, middleValid, rightValid, leftHeight,
                    rightHeight, _, _, _, _⟩
                have leftRowsValid : ∀ entry ∈ left.erase.toList,
                    ∀ row ∈ entry.2, row.WellFormed schema := by
                  intro entry member row rowMember
                  exact valid entry (by
                    simp only [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.mem_append]
                    exact Or.inl (Or.inl member)) row rowMember
                have middleRowsValid : ∀ entry ∈ middle.erase.toList,
                    ∀ row ∈ entry.2, row.WellFormed schema := by
                  intro entry member row rowMember
                  exact valid entry (by
                    simp only [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.mem_append]
                    exact Or.inl (Or.inr member)) row rowMember
                have rightRowsValid : ∀ entry ∈ right.erase.toList,
                    ∀ row ∈ entry.2, row.WellFormed schema := by
                  intro entry member row rowMember
                  exact valid entry (by
                    simp only [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.mem_append]
                    exact Or.inr member) row rowMember
                have leftDecoded :=
                  decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow schema source
                    left nextOverflow leftEncoding childFuel leftResult
                    leftTreeContains leftOverflowContains leftValid.rootValid
                    leftRowsValid (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    nextPositive
                    (by simp only [List.length_append] at pageBound; omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have middleDecoded :=
                  decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow schema source
                    middle leftEncoding.nextPage middleEncoding childFuel
                    middleResult middleTreeContains middleOverflowContains
                    middleValid.rootValid middleRowsValid (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    (by rw [leftNext]; omega)
                    (by
                      simp only [List.length_append] at pageBound
                      rw [leftNext]
                      omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have rightDecoded :=
                  decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow schema source
                    right middleEncoding.nextPage rightEncoding childFuel
                    rightResult rightTreeContains rightOverflowContains
                    rightValid.rootValid rightRowsValid (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    (by rw [middleNext, leftNext]; omega)
                    (by
                      simp only [List.length_append] at pageBound
                      rw [middleNext, leftNext]
                      omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                unfold CoreDecode.decodeSubtreeRowsFrom
                simp only [PersistentPageTree.Node.rootId]
                rw [rootRead]
                simp only [Option.bind_eq_bind, Option.bind]
                rw [interiorChildren_encodeChunkRoot_branch3 schema pageId left
                  firstSeparator middle secondSeparator right root rootResult]
                simp [leftDecoded, middleDecoded, rightDecoded,
                  CoreChunkPageState.Node.rows, PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList]

/-- The generated table encoder establishes the exact separator-routing
certificate consumed by the live primary-key range reader.  The statement
connects bytes, the persistent topology, logical in-order rows, and the
semantic no-skipped-match invariant in one refinement. -/
theorem decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow
    (schema : Core.Schema) (source : CoreDecode.PageSource) :
    ∀ (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
      (nextOverflow : Nat) (encoding : OverflowEncoding) (fuel : Nat),
      encodeChunkNodeWithOverflow schema node nextOverflow = some encoding →
      PageSourceContains source encoding.treePages →
      CoreDecode.ReadsPagesFrom source nextOverflow encoding.overflowPages →
      node.erase.RootValid →
      (∀ entry ∈ node.erase.toList, ∀ row ∈ entry.2,
        row.WellFormed schema) →
      (∀ pageId ∈ node.pageIds, 0 < pageId) →
      (CoreChunkPageState.Node.rows node).Pairwise Core.Row.keyLess →
      node.erase.height < fuel →
      0 < nextOverflow →
      nextOverflow + encoding.overflowPages.length < 2 ^ 32 →
      encoding.overflowPages.length < source.pageCount + 1 →
      ∃ tree,
        CoreDecode.decodeAbstractTableTreeFrom schema source fuel node.rootId =
          some tree ∧
        tree.toList = CoreChunkPageState.Node.rows node ∧
        tree.RangeWellRouted
  | .leaf pageId entries, nextOverflow, encoding, fuel, encoded, treeContains,
      overflowContains, _, valid, _, _, enough, nextPositive, pageBound,
      fuelBound => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases plansResult :
          (entries.flatMap fun entry => entry.2).mapM
            (CoreOverflow.tableCellPlan? schema) with
      | none => simp [plansResult] at encoded
      | some plans =>
        simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
        cases resolvedResult : CoreOverflow.resolvePlans nextOverflow plans with
        | none => simp [resolvedResult] at encoded
        | some resolved =>
          simp only [resolvedResult] at encoded
          cases pageResult : CoreFile.tableLeafPage? resolved.cells with
          | none => simp [pageResult] at encoded
          | some page =>
            simp only [pageResult, Option.some.injEq] at encoded
            subst encoding
            cases fuel with
            | zero =>
              simp [PersistentPageTree.Node.erase,
                RecursiveBPlusTree.Node.height] at enough
            | succ childFuel =>
              let rows := entries.flatMap fun entry => entry.2
              have rowsValid : ∀ row ∈ rows, row.WellFormed schema := by
                intro row member
                simp only [rows, List.mem_flatMap] at member
                rcases member with ⟨entry, entryMember, rowMember⟩
                exact valid entry (by simpa [PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList] using entryMember) row rowMember
              have rootRead : source.readPage pageId = some page.bytes :=
                treeContains ⟨pageId, page⟩ (by simp)
              have decoded := CoreDecode.decodeRowsFrom_resolvedLeaf schema source
                rows plans nextOverflow resolved page rowsValid
                (by simpa [rows] using plansResult) resolvedResult pageResult
                nextPositive (by simpa using pageBound)
                (by simpa using fuelBound) overflowContains
              refine ⟨CoreDecode.AbstractTableTree.leaf rows, ?_, rfl, ?_⟩
              · simp only [CoreDecode.decodeAbstractTableTreeFrom,
                  PersistentPageTree.Node.rootId]
                rw [rootRead]
                simp only [Option.bind_eq_bind, Option.bind]
                rw [decodeTableInterior_tableLeafPage pageResult, decoded]
                rfl
              · exact CoreDecode.AbstractTableTree.RangeWellRouted.leaf rows
  | .branch2 pageId left separator right, nextOverflow, encoding, fuel,
      encoded, treeContains, overflowContains, rootValid, valid, positive,
      ordered, enough, nextPositive, pageBound, fuelBound => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch2 pageId left separator right) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
        cases leftResult : encodeChunkNodeWithOverflow schema left
            nextOverflow with
        | none => simp [leftResult] at encoded
        | some leftEncoding =>
          simp only [leftResult] at encoded
          cases rightResult : encodeChunkNodeWithOverflow schema right
              leftEncoding.nextPage with
          | none => simp [rightResult] at encoded
          | some rightEncoding =>
            simp only [rightResult, Option.some.injEq] at encoded
            subst encoding
            cases fuel with
            | zero =>
              simp [PersistentPageTree.Node.erase,
                RecursiveBPlusTree.Node.height] at enough
            | succ childFuel =>
              have rootNumber := encodeChunkRoot_pageNumber schema
                (.branch2 pageId left separator right) root rootResult
              have rootNumber' : root.pageNumber = pageId := by
                simpa [PersistentPageTree.Node.rootId] using rootNumber
              have rootRead : source.readPage pageId = some root.page.bytes := by
                rw [← rootNumber']
                exact treeContains root (by simp)
              have leftTreeContains :
                  PageSourceContains source leftEncoding.treePages := by
                intro numbered member
                exact treeContains numbered (by simp [member])
              have rightTreeContains :
                  PageSourceContains source rightEncoding.treePages := by
                intro numbered member
                exact treeContains numbered (by simp [member])
              have leftOverflowContains : CoreDecode.ReadsPagesFrom source
                  nextOverflow leftEncoding.overflowPages :=
                CoreDecode.ReadsPagesFrom.left overflowContains
              have leftNext := encodeChunkNodeWithOverflow_nextPage schema left
                nextOverflow leftEncoding leftResult
              have rightOverflowContains : CoreDecode.ReadsPagesFrom source
                  leftEncoding.nextPage rightEncoding.overflowPages := by
                rw [leftNext]
                exact CoreDecode.ReadsPagesFrom.right overflowContains
              rcases rootValid with
                ⟨leftValid, rightValid, heights, _, _⟩
              have leftRowsValid : ∀ entry ∈ left.erase.toList,
                  ∀ row ∈ entry.2, row.WellFormed schema := by
                intro entry member row rowMember
                exact valid entry (by
                  simp only [PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.mem_append]
                  exact Or.inl member) row rowMember
              have rightRowsValid : ∀ entry ∈ right.erase.toList,
                  ∀ row ∈ entry.2, row.WellFormed schema := by
                intro entry member row rowMember
                exact valid entry (by
                  simp only [PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.mem_append]
                  exact Or.inr member) row rowMember
              have leftPositive : ∀ id ∈ left.pageIds, 0 < id := by
                intro id member
                apply positive id
                simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                  List.mem_append]
                exact Or.inl (Or.inr member)
              have rightPositive : ∀ id ∈ right.pageIds, 0 < id := by
                intro id member
                apply positive id
                simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                  List.mem_append]
                exact Or.inr member
              have childrenOrdered :
                  (CoreChunkPageState.Node.rows left ++
                    CoreChunkPageState.Node.rows right).Pairwise
                      Core.Row.keyLess := by
                simpa [CoreChunkPageState.Node.rows,
                  PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList, List.flatMap_append]
                  using ordered
              have leftCertificate :=
                decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow schema
                  source left nextOverflow leftEncoding childFuel leftResult
                  leftTreeContains leftOverflowContains leftValid.rootValid
                  leftRowsValid leftPositive
                  (List.pairwise_append.mp childrenOrdered).1 (by
                    simp [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.height] at enough
                    omega)
                  nextPositive
                  (by simp only [List.length_append] at pageBound; omega)
                  (by simp only [List.length_append] at fuelBound; omega)
              have rightCertificate :=
                decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow schema
                  source right leftEncoding.nextPage rightEncoding childFuel
                  rightResult rightTreeContains rightOverflowContains
                  rightValid.rootValid rightRowsValid rightPositive
                  (List.pairwise_append.mp childrenOrdered).2.1 (by
                    simp [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.height] at enough
                    omega)
                  (by rw [leftNext]; omega)
                  (by
                    simp only [List.length_append] at pageBound
                    rw [leftNext]
                    omega)
                  (by simp only [List.length_append] at fuelBound; omega)
              rcases leftCertificate with
                ⟨leftTree, leftDecoded, leftContents, leftRouted⟩
              rcases rightCertificate with
                ⟨rightTree, rightDecoded, rightContents, rightRouted⟩
              have leftRootPositive : 0 < left.rootId :=
                leftPositive left.rootId left.rootId_mem_pageIds
              rcases decodeTableInterior_encodeChunkRoot_branch2 schema pageId
                left separator right root leftRootPositive rootResult with
                ⟨boundary, boundaryLast, rootDecoded⟩
              have boundaryMember : boundary ∈
                  CoreChunkPageState.Node.rows left := by
                rcases List.getLast?_eq_some_iff.mp boundaryLast with
                  ⟨front, equal⟩
                rw [equal]
                simp
              have splitOrdered := List.pairwise_append.mp childrenOrdered
              refine ⟨CoreDecode.AbstractTableTree.branch2 leftTree
                boundary.rowid rightTree, ?_, ?_, ?_⟩
              · simp only [CoreDecode.decodeAbstractTableTreeFrom,
                  PersistentPageTree.Node.rootId]
                rw [rootRead]
                simp only [Option.bind_eq_bind, Option.bind, rootDecoded,
                  leftDecoded, rightDecoded]
              · simp [CoreDecode.AbstractTableTree.toList, leftContents,
                  rightContents, CoreChunkPageState.Node.rows,
                  PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList, List.flatMap_append]
              · apply CoreDecode.AbstractTableTree.RangeWellRouted.branch2
                  leftTree rightTree boundary.rowid leftRouted rightRouted
                · intro operation target row member matched
                  apply CoreDecode.table_range_upper_admitted row boundary.rowid
                    operation target _ matched
                  exact rowid_le_of_pairwise_last splitOrdered.1 boundaryLast
                    row (by simpa [leftContents] using member)
                · intro operation target row member matched
                  apply CoreDecode.table_range_lower_admitted boundary.rowid row
                    operation target _ matched
                  have after := splitOrdered.2.2 boundary boundaryMember row
                    (by simpa [rightContents] using member)
                  simpa [Core.Row.keyLess] using after
  | .branch3 pageId left firstSeparator middle secondSeparator right,
      nextOverflow, encoding, fuel, encoded, treeContains, overflowContains,
      rootValid, valid, positive, ordered, enough, nextPositive, pageBound,
      fuelBound => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch3 pageId left firstSeparator middle secondSeparator right) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
        cases leftResult : encodeChunkNodeWithOverflow schema left
            nextOverflow with
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
              cases fuel with
              | zero =>
                simp [PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.height] at enough
              | succ childFuel =>
                change CoreDecode.ReadsPagesFrom source nextOverflow
                  (leftEncoding.overflowPages ++ middleEncoding.overflowPages ++
                    rightEncoding.overflowPages) at overflowContains
                have rootNumber := encodeChunkRoot_pageNumber schema
                  (.branch3 pageId left firstSeparator middle secondSeparator
                    right) root rootResult
                have rootNumber' : root.pageNumber = pageId := by
                  simpa [PersistentPageTree.Node.rootId] using rootNumber
                have rootRead : source.readPage pageId = some root.page.bytes := by
                  rw [← rootNumber']
                  exact treeContains root (by simp)
                have leftTreeContains :
                    PageSourceContains source leftEncoding.treePages := by
                  intro numbered member
                  exact treeContains numbered (by simp [member])
                have middleTreeContains :
                    PageSourceContains source middleEncoding.treePages := by
                  intro numbered member
                  exact treeContains numbered (by simp [member])
                have rightTreeContains :
                    PageSourceContains source rightEncoding.treePages := by
                  intro numbered member
                  exact treeContains numbered (by simp [member])
                rw [List.append_assoc] at overflowContains
                have leftOverflowContains : CoreDecode.ReadsPagesFrom source
                    nextOverflow leftEncoding.overflowPages :=
                  CoreDecode.ReadsPagesFrom.left overflowContains
                have leftNext := encodeChunkNodeWithOverflow_nextPage schema left
                  nextOverflow leftEncoding leftResult
                have afterLeft : CoreDecode.ReadsPagesFrom source
                    leftEncoding.nextPage (middleEncoding.overflowPages ++
                      rightEncoding.overflowPages) := by
                  rw [leftNext]
                  exact CoreDecode.ReadsPagesFrom.right overflowContains
                have middleOverflowContains : CoreDecode.ReadsPagesFrom source
                    leftEncoding.nextPage middleEncoding.overflowPages :=
                  CoreDecode.ReadsPagesFrom.left afterLeft
                have middleNext := encodeChunkNodeWithOverflow_nextPage schema
                  middle leftEncoding.nextPage middleEncoding middleResult
                have rightOverflowContains : CoreDecode.ReadsPagesFrom source
                    middleEncoding.nextPage rightEncoding.overflowPages := by
                  rw [middleNext]
                  exact CoreDecode.ReadsPagesFrom.right afterLeft
                rcases rootValid with
                  ⟨leftValid, middleValid, rightValid, leftHeight,
                    rightHeight, _, _, _, _⟩
                have leftRowsValid : ∀ entry ∈ left.erase.toList,
                    ∀ row ∈ entry.2, row.WellFormed schema := by
                  intro entry member row rowMember
                  exact valid entry (by
                    simp only [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.mem_append]
                    exact Or.inl (Or.inl member)) row rowMember
                have middleRowsValid : ∀ entry ∈ middle.erase.toList,
                    ∀ row ∈ entry.2, row.WellFormed schema := by
                  intro entry member row rowMember
                  exact valid entry (by
                    simp only [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.mem_append]
                    exact Or.inl (Or.inr member)) row rowMember
                have rightRowsValid : ∀ entry ∈ right.erase.toList,
                    ∀ row ∈ entry.2, row.WellFormed schema := by
                  intro entry member row rowMember
                  exact valid entry (by
                    simp only [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.mem_append]
                    exact Or.inr member) row rowMember
                have leftPositive : ∀ id ∈ left.pageIds, 0 < id := by
                  intro id member
                  apply positive id
                  simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                    List.mem_append]
                  exact Or.inl (Or.inl (Or.inr member))
                have middlePositive : ∀ id ∈ middle.pageIds, 0 < id := by
                  intro id member
                  apply positive id
                  simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                    List.mem_append]
                  exact Or.inl (Or.inr member)
                have rightPositive : ∀ id ∈ right.pageIds, 0 < id := by
                  intro id member
                  apply positive id
                  simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                    List.mem_append]
                  exact Or.inr member
                have childrenOrdered :
                    (CoreChunkPageState.Node.rows left ++
                      CoreChunkPageState.Node.rows middle ++
                      CoreChunkPageState.Node.rows right).Pairwise
                        Core.Row.keyLess := by
                  simpa [CoreChunkPageState.Node.rows,
                    PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.flatMap_append,
                    List.append_assoc] using ordered
                have groupedOrdered :
                    (CoreChunkPageState.Node.rows left ++
                      (CoreChunkPageState.Node.rows middle ++
                        CoreChunkPageState.Node.rows right)).Pairwise
                          Core.Row.keyLess := by
                  simpa [List.append_assoc] using childrenOrdered
                have splitLeft := List.pairwise_append.mp groupedOrdered
                have splitMiddle := List.pairwise_append.mp splitLeft.2.1
                have leftCertificate :=
                  decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow schema
                    source left nextOverflow leftEncoding childFuel leftResult
                    leftTreeContains leftOverflowContains leftValid.rootValid
                    leftRowsValid leftPositive splitLeft.1 (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    nextPositive
                    (by simp only [List.length_append] at pageBound; omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have middleCertificate :=
                  decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow schema
                    source middle leftEncoding.nextPage middleEncoding childFuel
                    middleResult middleTreeContains middleOverflowContains
                    middleValid.rootValid middleRowsValid middlePositive
                    splitMiddle.1 (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    (by rw [leftNext]; omega)
                    (by
                      simp only [List.length_append] at pageBound
                      rw [leftNext]
                      omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have rightCertificate :=
                  decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow schema
                    source right middleEncoding.nextPage rightEncoding childFuel
                    rightResult rightTreeContains rightOverflowContains
                    rightValid.rootValid rightRowsValid rightPositive
                    splitMiddle.2.1 (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    (by rw [middleNext, leftNext]; omega)
                    (by
                      simp only [List.length_append] at pageBound
                      rw [middleNext, leftNext]
                      omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                rcases leftCertificate with
                  ⟨leftTree, leftDecoded, leftContents, leftRouted⟩
                rcases middleCertificate with
                  ⟨middleTree, middleDecoded, middleContents, middleRouted⟩
                rcases rightCertificate with
                  ⟨rightTree, rightDecoded, rightContents, rightRouted⟩
                have leftRootPositive : 0 < left.rootId :=
                  leftPositive left.rootId left.rootId_mem_pageIds
                have middleRootPositive : 0 < middle.rootId :=
                  middlePositive middle.rootId middle.rootId_mem_pageIds
                rcases decodeTableInterior_encodeChunkRoot_branch3 schema pageId
                  left firstSeparator middle secondSeparator right root
                  leftRootPositive middleRootPositive rootResult with
                  ⟨leftBoundary, middleBoundary, leftBoundaryLast,
                    middleBoundaryLast, rootDecoded⟩
                have leftBoundaryMember : leftBoundary ∈
                    CoreChunkPageState.Node.rows left := by
                  rcases List.getLast?_eq_some_iff.mp leftBoundaryLast with
                    ⟨front, equal⟩
                  rw [equal]
                  simp
                have middleBoundaryMember : middleBoundary ∈
                    CoreChunkPageState.Node.rows middle := by
                  rcases List.getLast?_eq_some_iff.mp middleBoundaryLast with
                    ⟨front, equal⟩
                  rw [equal]
                  simp
                refine ⟨CoreDecode.AbstractTableTree.branch3 leftTree
                  leftBoundary.rowid middleTree middleBoundary.rowid rightTree,
                  ?_, ?_, ?_⟩
                · simp only [CoreDecode.decodeAbstractTableTreeFrom,
                    PersistentPageTree.Node.rootId]
                  rw [rootRead]
                  simp only [Option.bind_eq_bind, Option.bind, rootDecoded,
                    leftDecoded, middleDecoded, rightDecoded]
                · simp [CoreDecode.AbstractTableTree.toList, leftContents,
                    middleContents, rightContents,
                    CoreChunkPageState.Node.rows,
                    PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.flatMap_append,
                    List.append_assoc]
                · apply CoreDecode.AbstractTableTree.RangeWellRouted.branch3
                    leftTree middleTree rightTree leftBoundary.rowid
                    middleBoundary.rowid leftRouted middleRouted rightRouted
                  · intro operation target row member matched
                    apply CoreDecode.table_range_upper_admitted row
                      leftBoundary.rowid operation target _ matched
                    exact rowid_le_of_pairwise_last splitLeft.1 leftBoundaryLast
                      row (by simpa [leftContents] using member)
                  · intro operation target row member matched
                    apply CoreDecode.table_range_middle_admitted
                      leftBoundary.rowid row middleBoundary.rowid operation target
                    · have after := splitLeft.2.2 leftBoundary
                          leftBoundaryMember row
                          (by
                            apply List.mem_append.mpr
                            exact Or.inl (by
                              simpa [middleContents] using member))
                      simpa [Core.Row.keyLess] using after
                    · exact rowid_le_of_pairwise_last splitMiddle.1
                        middleBoundaryLast row
                        (by simpa [middleContents] using member)
                    · exact matched
                  · intro operation target row member matched
                    apply CoreDecode.table_range_lower_admitted
                      middleBoundary.rowid row operation target _ matched
                    have after := splitMiddle.2.2 middleBoundary
                      middleBoundaryMember row
                      (by simpa [rightContents] using member)
                    simpa [Core.Row.keyLess] using after

/-- End-to-end exactness of generated primary-key range traversal.  This is
the theorem used to justify bypassing whole-database materialisation on the
stamped cold-read path. -/
theorem lookupTableRangeFrom_encodeChunkNodeWithOverflow_exact
    (schema : Core.Schema) (source : CoreDecode.PageSource)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (nextOverflow : Nat) (encoding : OverflowEncoding) (fuel : Nat)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (encoded : encodeChunkNodeWithOverflow schema node nextOverflow =
      some encoding)
    (treeContains : PageSourceContains source encoding.treePages)
    (overflowContains : CoreDecode.ReadsPagesFrom source nextOverflow
      encoding.overflowPages)
    (rootValid : node.erase.RootValid)
    (valid : ∀ entry ∈ node.erase.toList, ∀ row ∈ entry.2,
      row.WellFormed schema)
    (positive : ∀ pageId ∈ node.pageIds, 0 < pageId)
    (ordered : (CoreChunkPageState.Node.rows node).Pairwise Core.Row.keyLess)
    (enough : node.erase.height < fuel)
    (nextPositive : 0 < nextOverflow)
    (pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32)
    (fuelBound : encoding.overflowPages.length < source.pageCount + 1) :
    CoreDecode.lookupTableRangeFrom schema source operation target fuel
        node.rootId =
      some ((CoreChunkPageState.Node.rows node).filter
        (CoreDecode.tableRowMatchesRange operation target)) := by
  rcases decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow schema source
      node nextOverflow encoding fuel encoded treeContains overflowContains
      rootValid valid positive ordered enough nextPositive pageBound fuelBound with
    ⟨tree, decoded, contents, routed⟩
  rw [CoreDecode.lookupTableRangeFrom_decodeAbstract_exact schema source
    operation target fuel node.rootId tree decoded routed, contents]

theorem encodeChunkTablesWithOverflow_pageNumbers :
    ∀ (nextOverflow : Nat) (tables : List CoreChunkPageState.TableState)
      (encoding : OverflowEncoding),
      encodeChunkTablesWithOverflow nextOverflow tables = some encoding →
      encoding.treePages.map NumberedPage.pageNumber =
        CoreChunkPageState.tablePageIds tables
  | _, [], encoding, encoded => by
      simp only [encodeChunkTablesWithOverflow, Option.some.injEq] at encoded
      subst encoding
      rfl
  | nextOverflow, table :: tables, encoding, encoded => by
      simp only [encodeChunkTablesWithOverflow, Option.bind_eq_bind,
        Option.bind] at encoded
      cases headResult : encodeChunkNodeWithOverflow table.table.schema
          table.tree.root nextOverflow with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeChunkTablesWithOverflow head.nextPage tables with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst encoding
              simp only [List.map_append, CoreChunkPageState.tablePageIds,
                List.flatMap_cons]
              rw [encodeChunkNodeWithOverflow_pageNumbers table.table.schema
                table.tree.root nextOverflow head headResult,
                encodeChunkTablesWithOverflow_pageNumbers head.nextPage tables
                  tail tailResult]
              rfl

theorem encodeChunkTablesWithOverflow_nextPage :
    ∀ (nextOverflow : Nat) (tables : List CoreChunkPageState.TableState)
      (encoding : OverflowEncoding),
      encodeChunkTablesWithOverflow nextOverflow tables = some encoding →
      encoding.nextPage = nextOverflow + encoding.overflowPages.length
  | _, [], encoding, encoded => by
      simp only [encodeChunkTablesWithOverflow, Option.some.injEq] at encoded
      subst encoding
      simp
  | nextOverflow, table :: tables, encoding, encoded => by
      simp only [encodeChunkTablesWithOverflow, Option.bind_eq_bind,
        Option.bind] at encoded
      cases headResult : encodeChunkNodeWithOverflow table.table.schema
          table.tree.root nextOverflow with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeChunkTablesWithOverflow head.nextPage tables with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst encoding
              simp only [List.length_append]
              rw [encodeChunkTablesWithOverflow_nextPage head.nextPage tables
                tail tailResult,
                encodeChunkNodeWithOverflow_nextPage table.table.schema
                  table.tree.root nextOverflow head headResult]
              omega

theorem encodeChunkTables_pageNumbers :
    ∀ (tables : List CoreChunkPageState.TableState)
      (pages : List NumberedPage),
      encodeChunkTables tables = some pages →
      pages.map NumberedPage.pageNumber =
        CoreChunkPageState.tablePageIds tables
  | [], pages, encoded => by
      simp only [encodeChunkTables, Option.some.injEq] at encoded
      subst pages
      rfl
  | table :: tables, pages, encoded => by
      simp only [encodeChunkTables, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : encodeChunkTable table with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeChunkTables tables with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst pages
              simp only [List.map_append, CoreChunkPageState.tablePageIds,
                List.flatMap_cons]
              rw [show head.map NumberedPage.pageNumber = table.pageIds by
                exact encodeChunkNode_pageNumbers table.table.schema
                  table.tree.root head headResult]
              rw [encodeChunkTables_pageNumbers tables tail tailResult]
              rfl

def chunkTableCatalogEntry (state : CoreChunkPageState.TableState) :
    CoreFile.CatalogEntry := {
  kind := "table"
  name := state.table.schema.name
  table := state.table.schema.name
  rootPage := state.rootPage
  sql := CoreFile.tableSQL state.table.schema }

theorem decodeTableFrom_encodeChunkNodeWithOverflow
    (source : CoreDecode.PageSource) (state : CoreChunkPageState.TableState)
    (nextOverflow : Nat) (encoding : OverflowEncoding)
    (encoded : encodeChunkNodeWithOverflow state.table.schema
      state.tree.root nextOverflow = some encoding)
    (treeContains : PageSourceContains source encoding.treePages)
    (overflowContains : CoreDecode.ReadsPagesFrom source nextOverflow
      encoding.overflowPages)
    (heightBound : state.tree.root.erase.height < source.pageCount + 1)
    (nextPositive : 0 < nextOverflow)
    (pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32)
    (fuelBound : encoding.overflowPages.length < source.pageCount + 1) :
    CoreDecode.decodeTableFrom source
      (CoreDecode.CatalogEntry.ofEncoded (chunkTableCatalogEntry state)) =
        some state.table.withoutIndexes := by
  have rowsValid : ∀ entry ∈ state.tree.root.erase.toList,
      ∀ row ∈ entry.2, row.WellFormed state.table.schema := by
    intro entry entryMember row rowMember
    have member : row ∈ CoreChunkPageState.Node.rows state.tree.root := by
      unfold CoreChunkPageState.Node.rows
      simp only [List.mem_flatMap]
      exact ⟨entry, entryMember, rowMember⟩
    change row ∈ CoreChunkPageState.Store.rows state.tree at member
    rw [state.represents] at member
    exact state.table.rowsWellFormed.1 row member
  have decodedRows := decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow
    state.table.schema source state.tree.root nextOverflow encoding
    (source.pageCount + 1) encoded treeContains overflowContains
    state.tree.rootValid rowsValid heightBound nextPositive pageBound fuelBound
  unfold CoreDecode.decodeTableFrom chunkTableCatalogEntry
    CoreDecode.CatalogEntry.ofEncoded
  rw [dif_pos rfl]
  simp only [Option.bind_eq_bind, Option.bind]
  unfold CoreFile.tableSQL CoreChunkPageState.TableState.rootPage
  rw [CoreDecode.parseTableSchema_tableSQL state.table.schema
    (CanonicalSchemaSQL.Printable.ofWellFormed state.table.schema
      state.table.schemaWellFormed)]
  simp only [Option.bind_eq_bind, Option.bind]
  simp only [dif_pos True.intro]
  rw [decodedRows]
  simp only [Option.bind_eq_bind, Option.bind]
  change (Core.Table.rebuild state.table.schema []
    (CoreChunkPageState.Store.rows state.tree)).toOption = _
  rw [state.represents, Core.Table.rebuild_withoutIndexes]
  rfl

theorem decodeTablesFrom_encodeChunkTablesWithOverflow
    (source : CoreDecode.PageSource) :
    ∀ (nextOverflow : Nat) (tables : List CoreChunkPageState.TableState)
      (encoding : OverflowEncoding),
      encodeChunkTablesWithOverflow nextOverflow tables = some encoding →
      PageSourceContains source encoding.treePages →
      CoreDecode.ReadsPagesFrom source nextOverflow encoding.overflowPages →
      0 < nextOverflow →
      nextOverflow + encoding.overflowPages.length < 2 ^ 32 →
      encoding.overflowPages.length < source.pageCount + 1 →
      (∀ table ∈ tables,
        table.tree.root.erase.height < source.pageCount + 1) →
      (tables.map (fun table => CoreDecode.CatalogEntry.ofEncoded
        (chunkTableCatalogEntry table))).mapM
          (CoreDecode.decodeTableFrom source) =
        some (tables.map (fun table => table.table.withoutIndexes))
  | _, [], encoding, encoded, _, _, _, _, _, _ => by
      simp only [encodeChunkTablesWithOverflow, Option.some.injEq] at encoded
      subst encoding
      rfl
  | nextOverflow, table :: tables, encoding, encoded, treeContains,
      overflowContains, nextPositive, pageBound, fuelBound, heights => by
      simp only [encodeChunkTablesWithOverflow, Option.bind_eq_bind,
        Option.bind] at encoded
      cases headResult : encodeChunkNodeWithOverflow table.table.schema
          table.tree.root nextOverflow with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : encodeChunkTablesWithOverflow head.nextPage tables with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encoding
          have headTreeContains : PageSourceContains source head.treePages := by
            intro numbered member
            exact treeContains numbered (by simp [member])
          have tailTreeContains : PageSourceContains source tail.treePages := by
            intro numbered member
            exact treeContains numbered (by simp [member])
          have headOverflowContains : CoreDecode.ReadsPagesFrom source
              nextOverflow head.overflowPages :=
            CoreDecode.ReadsPagesFrom.left overflowContains
          have tailOverflowAt :=
            CoreDecode.ReadsPagesFrom.right overflowContains
          have headNext := encodeChunkNodeWithOverflow_nextPage
            table.table.schema table.tree.root nextOverflow head headResult
          have tailOverflowContains : CoreDecode.ReadsPagesFrom source
              head.nextPage tail.overflowPages := by
            simpa [headNext] using tailOverflowAt
          have headDecoded := decodeTableFrom_encodeChunkNodeWithOverflow
            source table nextOverflow head headResult headTreeContains
            headOverflowContains (heights table (by simp)) nextPositive
            (by simp only [List.length_append] at pageBound; omega)
            (by simp only [List.length_append] at fuelBound; omega)
          have tailDecoded := decodeTablesFrom_encodeChunkTablesWithOverflow
            source head.nextPage tables tail tailResult tailTreeContains
            tailOverflowContains (by rw [headNext]; omega)
            (by
              simp only [List.length_append] at pageBound
              rw [headNext]
              omega)
            (by simp only [List.length_append] at fuelBound; omega)
            (fun candidate member => heights candidate (by simp [member]))
          simp only [List.map_cons, List.mapM_cons, headDecoded, tailDecoded,
            Option.bind_eq_bind, Option.bind]
          rfl

/-- Exact point lookup for the live overflow-aware persistent table encoder.
The result covers both hits and valid misses and follows exactly one child at
each interior page. -/
theorem lookupTableRowidFrom_encodeChunkNodeWithOverflow
    (schema : Core.Schema) (source : CoreDecode.PageSource)
    (target : Core.Integer) :
    ∀ (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
      (nextOverflow : Nat) (encoding : OverflowEncoding) (fuel : Nat),
      encodeChunkNodeWithOverflow schema node nextOverflow = some encoding →
      PageSourceContains source encoding.treePages →
      CoreDecode.ReadsPagesFrom source nextOverflow encoding.overflowPages →
      node.erase.RootValid →
      (∀ entry ∈ node.erase.toList, ∀ row ∈ entry.2,
        row.WellFormed schema) →
      (∀ pageId ∈ node.pageIds, 0 < pageId) →
      (CoreChunkPageState.Node.rows node).Pairwise Core.Row.keyLess →
      node.erase.height < fuel →
      0 < nextOverflow →
      nextOverflow + encoding.overflowPages.length < 2 ^ 32 →
      encoding.overflowPages.length < source.pageCount + 1 →
      CoreDecode.lookupTableRowidFrom schema source target fuel node.rootId =
        some ((CoreChunkPageState.Node.rows node).find?
          fun row => row.rowid = target)
  | .leaf pageId entries, nextOverflow, encoding, fuel, encoded, treeContains,
      overflowContains, _, valid, _, _, enough, nextPositive, pageBound,
      fuelBound => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases plansResult :
          (entries.flatMap fun entry => entry.2).mapM
            (CoreOverflow.tableCellPlan? schema) with
      | none => simp [plansResult] at encoded
      | some plans =>
        simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
        cases resolvedResult : CoreOverflow.resolvePlans nextOverflow plans with
        | none => simp [resolvedResult] at encoded
        | some resolved =>
          simp only [resolvedResult] at encoded
          cases pageResult : CoreFile.tableLeafPage? resolved.cells with
          | none => simp [pageResult] at encoded
          | some page =>
            simp only [pageResult, Option.some.injEq] at encoded
            subst encoding
            cases fuel with
            | zero =>
              simp [PersistentPageTree.Node.erase,
                RecursiveBPlusTree.Node.height] at enough
            | succ childFuel =>
              let rows := entries.flatMap fun entry => entry.2
              have rowsValid : ∀ row ∈ rows, row.WellFormed schema := by
                intro row member
                simp only [rows, List.mem_flatMap] at member
                rcases member with ⟨entry, entryMember, rowMember⟩
                exact valid entry (by simpa [PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList] using entryMember) row rowMember
              have rootRead : source.readPage pageId = some page.bytes :=
                treeContains ⟨pageId, page⟩ (by simp)
              have decoded := CoreDecode.decodeRowsFrom_resolvedLeaf schema source
                rows plans nextOverflow resolved page rowsValid
                (by simpa [rows] using plansResult) resolvedResult pageResult
                nextPositive (by simpa using pageBound)
                (by simpa using fuelBound) overflowContains
              rw [CoreDecode.lookupTableRowidFrom_succ]
              simp only [PersistentPageTree.Node.rootId]
              rw [rootRead]
              simp only
              rw [decodeTableInterior_tableLeafPage pageResult, decoded]
              rfl
  | .branch2 pageId left separator right, nextOverflow, encoding, fuel,
      encoded, treeContains, overflowContains, rootValid, valid, positive,
      ordered, enough, nextPositive, pageBound, fuelBound => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch2 pageId left separator right) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
        cases leftResult : encodeChunkNodeWithOverflow schema left
            nextOverflow with
        | none => simp [leftResult] at encoded
        | some leftEncoding =>
          simp only [leftResult] at encoded
          cases rightResult : encodeChunkNodeWithOverflow schema right
              leftEncoding.nextPage with
          | none => simp [rightResult] at encoded
          | some rightEncoding =>
            simp only [rightResult, Option.some.injEq] at encoded
            subst encoding
            cases fuel with
            | zero =>
              simp [PersistentPageTree.Node.erase,
                RecursiveBPlusTree.Node.height] at enough
            | succ childFuel =>
              have rootNumber := encodeChunkRoot_pageNumber schema
                (.branch2 pageId left separator right) root rootResult
              have rootNumber' : root.pageNumber = pageId := by
                simpa [PersistentPageTree.Node.rootId] using rootNumber
              have rootRead : source.readPage pageId = some root.page.bytes := by
                rw [← rootNumber']
                exact treeContains root (by simp)
              have leftTreeContains :
                  PageSourceContains source leftEncoding.treePages := by
                intro numbered member
                exact treeContains numbered (by simp [member])
              have rightTreeContains :
                  PageSourceContains source rightEncoding.treePages := by
                intro numbered member
                exact treeContains numbered (by simp [member])
              have leftOverflowContains : CoreDecode.ReadsPagesFrom source
                  nextOverflow leftEncoding.overflowPages :=
                CoreDecode.ReadsPagesFrom.left overflowContains
              have leftNext := encodeChunkNodeWithOverflow_nextPage schema left
                nextOverflow leftEncoding leftResult
              have rightOverflowContains : CoreDecode.ReadsPagesFrom source
                  leftEncoding.nextPage rightEncoding.overflowPages := by
                rw [leftNext]
                exact CoreDecode.ReadsPagesFrom.right overflowContains
              rcases rootValid with
                ⟨leftValid, rightValid, heights, _, _⟩
              have leftRowsValid : ∀ entry ∈ left.erase.toList,
                  ∀ row ∈ entry.2, row.WellFormed schema := by
                intro entry member row rowMember
                exact valid entry (by
                  simp only [PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.mem_append]
                  exact Or.inl member) row rowMember
              have rightRowsValid : ∀ entry ∈ right.erase.toList,
                  ∀ row ∈ entry.2, row.WellFormed schema := by
                intro entry member row rowMember
                exact valid entry (by
                  simp only [PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.mem_append]
                  exact Or.inr member) row rowMember
              have leftPositive : ∀ id ∈ left.pageIds, 0 < id := by
                intro id member
                apply positive id
                simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                  List.mem_append]
                exact Or.inl (Or.inr member)
              have rightPositive : ∀ id ∈ right.pageIds, 0 < id := by
                intro id member
                apply positive id
                simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                  List.mem_append]
                exact Or.inr member
              have childrenOrdered :
                  (CoreChunkPageState.Node.rows left ++
                    CoreChunkPageState.Node.rows right).Pairwise
                      Core.Row.keyLess := by
                simpa [CoreChunkPageState.Node.rows,
                  PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList, List.flatMap_append]
                  using ordered
              have leftLookup :=
                lookupTableRowidFrom_encodeChunkNodeWithOverflow schema source
                  target left nextOverflow leftEncoding childFuel leftResult
                  leftTreeContains leftOverflowContains leftValid.rootValid
                  leftRowsValid leftPositive
                  (List.pairwise_append.mp childrenOrdered).1 (by
                    simp [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.height] at enough
                    omega)
                  nextPositive
                  (by simp only [List.length_append] at pageBound; omega)
                  (by simp only [List.length_append] at fuelBound; omega)
              have rightLookup :=
                lookupTableRowidFrom_encodeChunkNodeWithOverflow schema source
                  target right leftEncoding.nextPage rightEncoding childFuel
                  rightResult rightTreeContains rightOverflowContains
                  rightValid.rootValid rightRowsValid rightPositive
                  (List.pairwise_append.mp childrenOrdered).2.1 (by
                    simp [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.height] at enough
                    omega)
                  (by rw [leftNext]; omega)
                  (by
                    simp only [List.length_append] at pageBound
                    rw [leftNext]
                    omega)
                  (by simp only [List.length_append] at fuelBound; omega)
              have leftRootPositive : 0 < left.rootId :=
                leftPositive left.rootId left.rootId_mem_pageIds
              rcases decodeTableInterior_encodeChunkRoot_branch2 schema pageId
                left separator right root leftRootPositive rootResult with
                ⟨boundary, boundaryLast, rootDecoded⟩
              have routing := findRowid_append_routed target boundary.rowid
                (CoreChunkPageState.Node.rows left)
                (CoreChunkPageState.Node.rows right) childrenOrdered
                (by rw [boundaryLast]; rfl)
              rw [CoreDecode.lookupTableRowidFrom_succ]
              simp only [PersistentPageTree.Node.rootId]
              rw [rootRead]
              simp only
              rw [rootDecoded]
              by_cases routed : target.value ≤ boundary.rowid.value
              · have findEqual := routing
                simp only [if_pos routed] at findEqual
                simpa [CoreDecode.tableChildForRowid, routed, leftLookup,
                  findRowid, CoreChunkPageState.Node.rows,
                  PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList, List.flatMap_append]
                  using congrArg some findEqual.symm
              · have findEqual := routing
                simp only [if_neg routed] at findEqual
                simpa [CoreDecode.tableChildForRowid, routed, rightLookup,
                  findRowid, CoreChunkPageState.Node.rows,
                  PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList, List.flatMap_append]
                  using congrArg some findEqual.symm
  | .branch3 pageId left firstSeparator middle secondSeparator right,
      nextOverflow, encoding, fuel, encoded, treeContains, overflowContains,
      rootValid, valid, positive, ordered, enough, nextPositive, pageBound,
      fuelBound => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch3 pageId left firstSeparator middle secondSeparator right) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
        cases leftResult : encodeChunkNodeWithOverflow schema left
            nextOverflow with
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
              cases fuel with
              | zero =>
                simp [PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.height] at enough
              | succ childFuel =>
                have rootNumber := encodeChunkRoot_pageNumber schema
                  (.branch3 pageId left firstSeparator middle secondSeparator
                    right) root rootResult
                have rootNumber' : root.pageNumber = pageId := by
                  simpa [PersistentPageTree.Node.rootId] using rootNumber
                have rootRead : source.readPage pageId = some root.page.bytes := by
                  rw [← rootNumber']
                  exact treeContains root (by simp)
                have leftTreeContains :
                    PageSourceContains source leftEncoding.treePages := by
                  intro numbered member
                  exact treeContains numbered (by simp [member])
                have middleTreeContains :
                    PageSourceContains source middleEncoding.treePages := by
                  intro numbered member
                  exact treeContains numbered (by simp [member])
                have rightTreeContains :
                    PageSourceContains source rightEncoding.treePages := by
                  intro numbered member
                  exact treeContains numbered (by simp [member])
                have normalizedOverflow : CoreDecode.ReadsPagesFrom source
                    nextOverflow (leftEncoding.overflowPages ++
                      (middleEncoding.overflowPages ++
                        rightEncoding.overflowPages)) := by
                  simpa [List.append_assoc] using overflowContains
                have leftOverflowContains : CoreDecode.ReadsPagesFrom source
                    nextOverflow leftEncoding.overflowPages :=
                  CoreDecode.ReadsPagesFrom.left normalizedOverflow
                have afterLeft := CoreDecode.ReadsPagesFrom.right
                  normalizedOverflow
                have leftNext := encodeChunkNodeWithOverflow_nextPage schema left
                  nextOverflow leftEncoding leftResult
                have middleOverflowContains : CoreDecode.ReadsPagesFrom source
                    leftEncoding.nextPage middleEncoding.overflowPages := by
                  rw [leftNext]
                  exact CoreDecode.ReadsPagesFrom.left afterLeft
                have afterMiddle := CoreDecode.ReadsPagesFrom.right afterLeft
                have middleNext := encodeChunkNodeWithOverflow_nextPage schema
                  middle leftEncoding.nextPage middleEncoding middleResult
                have rightOverflowContains : CoreDecode.ReadsPagesFrom source
                    middleEncoding.nextPage rightEncoding.overflowPages := by
                  rw [middleNext, leftNext]
                  exact afterMiddle
                rcases rootValid with
                  ⟨leftValid, middleValid, rightValid, leftHeight,
                    rightHeight, _, _, _, _⟩
                have leftRowsValid : ∀ entry ∈ left.erase.toList,
                    ∀ row ∈ entry.2, row.WellFormed schema := by
                  intro entry member row rowMember
                  exact valid entry (by
                    simp only [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.mem_append]
                    exact Or.inl (Or.inl member)) row rowMember
                have middleRowsValid : ∀ entry ∈ middle.erase.toList,
                    ∀ row ∈ entry.2, row.WellFormed schema := by
                  intro entry member row rowMember
                  exact valid entry (by
                    simp only [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.mem_append]
                    exact Or.inl (Or.inr member)) row rowMember
                have rightRowsValid : ∀ entry ∈ right.erase.toList,
                    ∀ row ∈ entry.2, row.WellFormed schema := by
                  intro entry member row rowMember
                  exact valid entry (by
                    simp only [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.mem_append]
                    exact Or.inr member) row rowMember
                have leftPositive : ∀ id ∈ left.pageIds, 0 < id := by
                  intro id member
                  apply positive id
                  simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                    List.mem_append]
                  exact Or.inl (Or.inl (Or.inr member))
                have middlePositive : ∀ id ∈ middle.pageIds, 0 < id := by
                  intro id member
                  apply positive id
                  simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                    List.mem_append]
                  exact Or.inl (Or.inr member)
                have rightPositive : ∀ id ∈ right.pageIds, 0 < id := by
                  intro id member
                  apply positive id
                  simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                    List.mem_append]
                  exact Or.inr member
                have childrenOrdered :
                    (CoreChunkPageState.Node.rows left ++
                      CoreChunkPageState.Node.rows middle ++
                      CoreChunkPageState.Node.rows right).Pairwise
                        Core.Row.keyLess := by
                  simpa [CoreChunkPageState.Node.rows,
                    PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.flatMap_append,
                    List.append_assoc] using ordered
                have firstSplit := List.pairwise_append.mp (show
                  (CoreChunkPageState.Node.rows left ++
                    (CoreChunkPageState.Node.rows middle ++
                      CoreChunkPageState.Node.rows right)).Pairwise
                        Core.Row.keyLess from by
                    simpa only [List.append_assoc] using childrenOrdered)
                have middleRightOrdered :
                    (CoreChunkPageState.Node.rows middle ++
                      CoreChunkPageState.Node.rows right).Pairwise
                        Core.Row.keyLess := firstSplit.2.1
                have secondSplit := List.pairwise_append.mp middleRightOrdered
                have leftLookup :=
                  lookupTableRowidFrom_encodeChunkNodeWithOverflow schema source
                    target left nextOverflow leftEncoding childFuel leftResult
                    leftTreeContains leftOverflowContains leftValid.rootValid
                    leftRowsValid leftPositive firstSplit.1 (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    nextPositive
                    (by simp only [List.length_append] at pageBound; omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have middleLookup :=
                  lookupTableRowidFrom_encodeChunkNodeWithOverflow schema source
                    target middle leftEncoding.nextPage middleEncoding childFuel
                    middleResult middleTreeContains middleOverflowContains
                    middleValid.rootValid middleRowsValid middlePositive
                    secondSplit.1 (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    (by rw [leftNext]; omega)
                    (by
                      simp only [List.length_append] at pageBound
                      rw [leftNext]
                      omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have rightLookup :=
                  lookupTableRowidFrom_encodeChunkNodeWithOverflow schema source
                    target right middleEncoding.nextPage rightEncoding childFuel
                    rightResult rightTreeContains rightOverflowContains
                    rightValid.rootValid rightRowsValid rightPositive
                    secondSplit.2.1 (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    (by rw [middleNext, leftNext]; omega)
                    (by
                      simp only [List.length_append] at pageBound
                      rw [middleNext, leftNext]
                      omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have leftRootPositive : 0 < left.rootId :=
                  leftPositive left.rootId left.rootId_mem_pageIds
                have middleRootPositive : 0 < middle.rootId :=
                  middlePositive middle.rootId middle.rootId_mem_pageIds
                rcases decodeTableInterior_encodeChunkRoot_branch3 schema pageId
                  left firstSeparator middle secondSeparator right root
                  leftRootPositive middleRootPositive rootResult with
                  ⟨leftBoundary, middleBoundary, leftLast, middleLast,
                    rootDecoded⟩
                have firstRouting := findRowid_append_routed target
                  leftBoundary.rowid (CoreChunkPageState.Node.rows left)
                  (CoreChunkPageState.Node.rows middle ++
                    CoreChunkPageState.Node.rows right)
                  (show (CoreChunkPageState.Node.rows left ++
                    (CoreChunkPageState.Node.rows middle ++
                      CoreChunkPageState.Node.rows right)).Pairwise
                        Core.Row.keyLess from by
                    simpa only [List.append_assoc] using childrenOrdered)
                  (by rw [leftLast]; rfl)
                have secondRouting := findRowid_append_routed target
                  middleBoundary.rowid (CoreChunkPageState.Node.rows middle)
                  (CoreChunkPageState.Node.rows right) middleRightOrdered
                  (by rw [middleLast]; rfl)
                rw [CoreDecode.lookupTableRowidFrom_succ]
                simp only [PersistentPageTree.Node.rootId]
                rw [rootRead]
                simp only
                rw [rootDecoded]
                by_cases leftRoute : target.value ≤ leftBoundary.rowid.value
                · have findEqual := firstRouting
                  simp only [if_pos leftRoute] at findEqual
                  simpa [CoreDecode.tableChildForRowid, leftRoute, leftLookup,
                    findRowid, CoreChunkPageState.Node.rows,
                    PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.flatMap_append,
                    List.append_assoc] using congrArg some findEqual.symm
                · by_cases middleRoute :
                      target.value ≤ middleBoundary.rowid.value
                  · have firstEqual := firstRouting
                    simp only [if_neg leftRoute] at firstEqual
                    have secondEqual := secondRouting
                    simp only [if_pos middleRoute] at secondEqual
                    have findEqual := firstEqual.trans secondEqual
                    simpa [CoreDecode.tableChildForRowid, leftRoute,
                      middleRoute, middleLookup, findRowid,
                      CoreChunkPageState.Node.rows,
                      PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.flatMap_append,
                      List.append_assoc] using congrArg some findEqual.symm
                  · have firstEqual := firstRouting
                    simp only [if_neg leftRoute] at firstEqual
                    have secondEqual := secondRouting
                    simp only [if_neg middleRoute] at secondEqual
                    have findEqual := firstEqual.trans secondEqual
                    simpa [CoreDecode.tableChildForRowid, leftRoute,
                      middleRoute, rightLookup, findRowid,
                      CoreChunkPageState.Node.rows,
                      PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.flatMap_append,
                      List.append_assoc] using congrArg some findEqual.symm

def orderNumberedPages (pages : List NumberedPage) : List NumberedPage :=
  pages.mergeSort (fun left right => left.pageNumber ≤ right.pageNumber)

theorem orderNumberedPages_eq_of_range {pages : List NumberedPage}
    {start count : Nat}
    (numbers : pages.map NumberedPage.pageNumber = List.range' start count) :
    orderNumberedPages pages = pages := by
  unfold orderNumberedPages
  apply List.mergeSort_of_sorted
  apply (List.pairwise_map (f := NumberedPage.pageNumber)
    (R := fun left right : Nat => decide (left ≤ right) = true)).mp
  rw [numbers]
  exact List.pairwise_le_range'.imp fun less => by simpa using less

/-- Encode from a persistent table state already proved to represent the input
database.  Keeping this phase separate lets the live commit retain the exact
state whose page identities the encoder serialized. -/
def encodeBulkFromState (database : Core.Database)
    (state : CoreChunkPageState.State) : Option CoreFile.Image := do
  let tableEncoding ← encodeChunkTablesWithOverflow state.nextPage state.tables
  let indexEncodings ← CoreOverflow.encodeIndexTableGroups
    tableEncoding.nextPage database.tables
  let entries := state.tables.map chunkTableCatalogEntry ++
    CoreOverflow.indexEntriesOf indexEncodings
  -- `State.build?` assigns page identities in preorder, and
  -- `encodeChunkTables_pageNumbers` proves this list is already the contiguous
  -- allocation interval.  No runtime sort is needed to recover file order.
  let remaining := tableEncoding.treePages.map NumberedPage.page ++
    tableEncoding.overflowPages ++
    CoreOverflow.indexPagesOf indexEncodings
  let total := 1 + remaining.length
  if countBound : total + 1 < 2 ^ 32 then
    let count : FileFormat.U32Value := ⟨total, by omega⟩
    let schema ← CoreFile.schemaPageForEntries? entries count
    some ⟨database, schema :: remaining⟩
  else none

/-- Bulk encoder for the new representation.  Table page identities come from
`CorePageState`; physical index B-trees are appended using the existing
overflow-aware index encoder until stable identified index pages land. -/
def encodeBulk (database : Core.Database) : Option CoreFile.Image := do
  let state ← CoreChunkPageState.State.build? database
  encodeBulkFromState database state

/-- The live writer's bulk result retains the persistent state used by the
encoder, avoiding a second construction pass after the bytes are committed. -/
def encodeBulkWithState (database : Core.Database) :
    Option (CoreFile.Image × CoreChunkPageState.State) := do
  let state ← CoreChunkPageState.State.build? database
  let image ← encodeBulkFromState database state
  some (image, state)

theorem encodeBulkWithState_image {database : Core.Database}
    {result : CoreFile.Image × CoreChunkPageState.State}
    (encoded : encodeBulkWithState database = some result) :
    encodeBulk database = some result.1 := by
  unfold encodeBulkWithState at encoded
  rcases Option.bind_eq_some.mp encoded with ⟨state, stateResult, encoded⟩
  rcases Option.bind_eq_some.mp encoded with ⟨image, imageResult, encoded⟩
  simp only [Option.some.injEq] at encoded
  subst result
  unfold encodeBulk
  rw [stateResult]
  exact imageResult

theorem encodeBulkWithState_represents {database : Core.Database}
    {result : CoreFile.Image × CoreChunkPageState.State}
    (encoded : encodeBulkWithState database = some result) :
    result.2.Represents database := by
  unfold encodeBulkWithState at encoded
  rcases Option.bind_eq_some.mp encoded with ⟨state, stateResult, encoded⟩
  rcases Option.bind_eq_some.mp encoded with ⟨image, imageResult, encoded⟩
  simp only [Option.some.injEq] at encoded
  subst result
  exact CoreChunkPageState.State.build?_represents stateResult

theorem encodeBulk_database {database : Core.Database} {image : CoreFile.Image}
    (encoded : encodeBulk database = some image) : image.database = database := by
  unfold encodeBulk encodeBulkFromState at encoded
  cases stateResult : CoreChunkPageState.State.build? database with
  | none => simp [stateResult] at encoded
  | some state =>
      simp only [stateResult, Option.bind_eq_bind, Option.bind] at encoded
      cases tableResult : encodeChunkTablesWithOverflow state.nextPage
          state.tables with
      | none => simp [tableResult] at encoded
      | some tableEncoding =>
          simp only [tableResult] at encoded
          cases indexResult : CoreOverflow.encodeIndexTableGroups
              tableEncoding.nextPage database.tables with
          | none => simp [indexResult] at encoded
          | some indexes =>
              simp only [indexResult] at encoded
              split at encoded
              next bound =>
                let entries := state.tables.map chunkTableCatalogEntry ++
                  CoreOverflow.indexEntriesOf indexes
                let remaining := tableEncoding.treePages.map NumberedPage.page ++
                  tableEncoding.overflowPages ++
                  CoreOverflow.indexPagesOf indexes
                let count : FileFormat.U32Value :=
                  ⟨1 + remaining.length, by
                    change 1 + remaining.length < 2 ^ 32
                    simp only [remaining]
                    omega⟩
                change (do
                  let schema ← CoreFile.schemaPageForEntries? entries count
                  some ⟨database, schema :: remaining⟩) = some image at encoded
                cases schemaResult : CoreFile.schemaPageForEntries? entries count with
                | none => simp [schemaResult] at encoded
                | some schema =>
                    rw [schemaResult] at encoded
                    simp only [Option.bind_eq_bind, Option.bind,
                      Option.some.injEq] at encoded
                    subst image
                    rfl
              next => contradiction

theorem encodeBulk_header {database : Core.Database} {image : CoreFile.Image}
    (encoded : encodeBulk database = some image) :
    ∃ (count : FileFormat.U32Value) (schema : CoreFile.Page)
      (remaining : List CoreFile.Page) (body : List UInt8),
      image.pages = schema :: remaining ∧
      image.pageCount = count.val ∧
      schema.bytes = FileFormat.encodeDatabaseHeader
        (CoreFile.databaseHeader count) ++ body := by
  unfold encodeBulk encodeBulkFromState at encoded
  cases stateResult : CoreChunkPageState.State.build? database with
  | none => simp [stateResult] at encoded
  | some state =>
      simp only [stateResult, Option.bind_eq_bind, Option.bind] at encoded
      cases tableResult : encodeChunkTablesWithOverflow state.nextPage
          state.tables with
      | none => simp [tableResult] at encoded
      | some tableEncoding =>
        simp only [tableResult] at encoded
        cases indexResult : CoreOverflow.encodeIndexTableGroups
            tableEncoding.nextPage database.tables with
        | none => simp [indexResult] at encoded
        | some indexEncodings =>
          simp only [indexResult] at encoded
          split at encoded
          next countBound =>
            let entries := state.tables.map chunkTableCatalogEntry ++
              CoreOverflow.indexEntriesOf indexEncodings
            let remaining := tableEncoding.treePages.map NumberedPage.page ++
              tableEncoding.overflowPages ++
              CoreOverflow.indexPagesOf indexEncodings
            let count : FileFormat.U32Value := ⟨1 + remaining.length, by
              simp only [remaining, List.length_append, List.length_map]
              simp only [List.length_append, List.length_map] at countBound
              omega⟩
            change (do
              let schema ← CoreFile.schemaPageForEntries? entries count
              some ⟨database, schema :: remaining⟩) = some image at encoded
            cases schemaResult : CoreFile.schemaPageForEntries? entries count with
            | none => simp [schemaResult] at encoded
            | some schema =>
              rw [schemaResult] at encoded
              simp only [Option.bind_eq_bind, Option.bind,
                Option.some.injEq] at encoded
              subst image
              rcases CoreFile.schemaPageForEntries_header schemaResult with
                ⟨body, header⟩
              refine ⟨count, schema, remaining, body, rfl, ?_, header⟩
              simp [CoreFile.Image.pageCount, count, remaining, Nat.add_comm]
          next => contradiction

/-- The generated schema B-tree has the same meaning after replacing only its
100-byte database header.  This is the catalog bridge used by SQLite freelist
images, whose size/freelist fields differ from the canonical bulk image. -/
theorem decodeCatalogForOpen_encodeBulk_replaceHeader
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : encodeBulk database = some image)
    (first : CoreFile.Page) (remainingPages : List CoreFile.Page)
    (pagesEqual : image.pages = first :: remainingPages)
    (headerBytes : List UInt8) (headerLength : headerBytes.length = 100) :
    CoreDecode.decodeCatalogForOpen (headerBytes ++ first.bytes.drop 100) =
      CoreDecode.decodeCatalogForOpen first.bytes := by
  unfold encodeBulk encodeBulkFromState at encoded
  cases stateResult : CoreChunkPageState.State.build? database with
  | none => simp [stateResult] at encoded
  | some state =>
      simp only [stateResult, Option.bind_eq_bind, Option.bind] at encoded
      cases tableResult : encodeChunkTablesWithOverflow state.nextPage
          state.tables with
      | none => simp [tableResult] at encoded
      | some tableEncoding =>
          simp only [tableResult] at encoded
          cases indexResult : CoreOverflow.encodeIndexTableGroups
              tableEncoding.nextPage database.tables with
          | none => simp [indexResult] at encoded
          | some indexEncodings =>
              simp only [indexResult] at encoded
              split at encoded
              next countBound =>
                let entries := state.tables.map chunkTableCatalogEntry ++
                  CoreOverflow.indexEntriesOf indexEncodings
                let pages := tableEncoding.treePages.map NumberedPage.page ++
                  tableEncoding.overflowPages ++
                  CoreOverflow.indexPagesOf indexEncodings
                let count : FileFormat.U32Value := ⟨1 + pages.length, by
                  simp only [pages, List.length_append, List.length_map]
                  simp only [List.length_append, List.length_map] at countBound
                  omega⟩
                change (do
                  let schema ← CoreFile.schemaPageForEntries? entries count
                  some ⟨database, schema :: pages⟩) = some image at encoded
                cases schemaResult : CoreFile.schemaPageForEntries? entries count with
                | none => simp [schemaResult] at encoded
                | some schema =>
                    rw [schemaResult] at encoded
                    simp only [Option.bind_eq_bind, Option.bind,
                      Option.some.injEq] at encoded
                    subst image
                    simp only at pagesEqual
                    injection pagesEqual with firstEqual
                    subst first
                    have safe : ∀ entry ∈ entries,
                        CoreDecode.CatalogTextRoundtrips entry := by
                      intro entry _
                      exact ⟨utf8 entry.kind, utf8 entry.name,
                        utf8 entry.table, utf8 entry.sql⟩
                    exact
                      (CoreDecode.decodeCatalogForOpen_schemaPageForEntries_withHeader
                        entries count headerBytes headerLength safe
                        schemaResult).trans
                      (CoreDecode.decodeCatalogForOpen_schemaPageForEntries
                        entries count safe schemaResult).symm
              next => contradiction

/-- The live store-owned bulk image is a left inverse of the general page
decoder, up to the intentional canonical rebuilding of proof-carrying row
trees.  Every table and promoted index entry is decoded from its actual page
interval; no re-encoding comparison appears in the statement or proof. -/
theorem pageSourceRepresents_encodeBulk_in
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : encodeBulk database = some image)
    (source : CoreDecode.PageSource)
    (catalogRead :
      source.readPage 1 >>= CoreDecode.decodeCatalogForOpen =
        (CoreDecode.PageSource.ofList
          (image.pages.map CoreFile.Page.bytes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen)
    (activeTailReads : CoreDecode.ReadsPagesFrom source 2 image.pages.tail)
    (enoughPages : image.pageCount ≤ source.pageCount) :
    CoreDecode.PageSourceRepresents source database := by
  unfold encodeBulk encodeBulkFromState at encoded
  cases stateResult : CoreChunkPageState.State.build? database with
  | none => simp [stateResult] at encoded
  | some state =>
      simp only [stateResult, Option.bind_eq_bind, Option.bind] at encoded
      cases tableResult : encodeChunkTablesWithOverflow state.nextPage
          state.tables with
      | none => simp [tableResult] at encoded
      | some tableEncoding =>
        simp only [tableResult] at encoded
        cases indexResult : CoreOverflow.encodeIndexTableGroups
            tableEncoding.nextPage database.tables with
        | none => simp [indexResult] at encoded
        | some indexEncodings =>
          simp only [indexResult] at encoded
          split at encoded
          next countBound =>
            let tableEntries := state.tables.map chunkTableCatalogEntry
            let indexEntries := CoreOverflow.indexEntriesOf indexEncodings
            let entries := tableEntries ++ indexEntries
            let treePages :=
              tableEncoding.treePages.map NumberedPage.page
            let indexPages := CoreOverflow.indexPagesOf indexEncodings
            let remaining := treePages ++ tableEncoding.overflowPages ++
              indexPages
            let count : FileFormat.U32Value := ⟨1 + remaining.length, by
              change 1 + remaining.length < 2 ^ 32
              simp only [remaining, treePages, indexPages]
              omega⟩
            change (do
              let schema ← CoreFile.schemaPageForEntries? entries count
              some ⟨database, schema :: remaining⟩) = some image at encoded
            cases schemaResult : CoreFile.schemaPageForEntries? entries count with
            | none =>
                simp [schemaResult] at encoded
            | some schemaPage =>
              rw [schemaResult] at encoded
              simp only [Option.bind_eq_bind, Option.bind,
                Option.some.injEq] at encoded
              subst image
              obtain ⟨tablePageCount, stateNext, statePages⟩ :=
                CoreChunkPageState.State.build?_interval stateResult
              have treeNumbers := encodeChunkTablesWithOverflow_pageNumbers
                state.nextPage state.tables tableEncoding tableResult
              rw [statePages] at treeNumbers
              have treeLength : treePages.length = tablePageCount := by
                have lengths := congrArg List.length treeNumbers
                simpa [treePages] using lengths
              have tableNext := encodeChunkTablesWithOverflow_nextPage
                state.nextPage state.tables tableEncoding tableResult
              have sourceCountLower : 1 + remaining.length ≤ source.pageCount := by
                simpa [CoreFile.Image.pageCount, Nat.add_comm] using enoughPages
              have remainingReads : CoreDecode.ReadsPagesFrom source 2
                  remaining := by
                simpa using activeTailReads
              have treeReads : CoreDecode.ReadsPagesFrom source 2 treePages := by
                apply CoreDecode.ReadsPagesFrom.left
                  (right := tableEncoding.overflowPages ++ indexPages)
                simpa [remaining, List.append_assoc] using remainingReads
              have treeContains : PageSourceContains source
                  tableEncoding.treePages := by
                apply PageSourceContains.ofReadsRange source 2
                · have numberedLength : tableEncoding.treePages.length =
                      tablePageCount := by
                    simpa [treePages] using treeLength
                  rw [numberedLength]
                  exact treeNumbers
                · exact treeReads
              have overflowReads : CoreDecode.ReadsPagesFrom source
                  state.nextPage tableEncoding.overflowPages := by
                have afterTree := CoreDecode.ReadsPagesFrom.right
                  (left := treePages)
                  (right := tableEncoding.overflowPages ++ indexPages)
                  (by simpa [remaining, List.append_assoc] using remainingReads)
                have overflow := CoreDecode.ReadsPagesFrom.left afterTree
                simpa [stateNext, treeLength, Nat.add_comm, Nat.add_left_comm,
                  Nat.add_assoc] using overflow
              have indexReads : CoreDecode.ReadsPagesFrom source
                  tableEncoding.nextPage indexPages := by
                have afterTree := CoreDecode.ReadsPagesFrom.right
                  (left := treePages)
                  (right := tableEncoding.overflowPages ++ indexPages)
                  (by simpa [remaining, List.append_assoc] using remainingReads)
                have afterOverflow := CoreDecode.ReadsPagesFrom.right
                  (left := tableEncoding.overflowPages) (right := indexPages)
                  afterTree
                simpa [tableNext, stateNext, treeLength, Nat.add_comm,
                  Nat.add_left_comm, Nat.add_assoc] using afterOverflow
              have individualIndexReads : ∀ encoding ∈ indexEncodings,
                  CoreDecode.ReadsPagesFrom source encoding.rootPage
                    encoding.pages :=
                CoreDecode.ReadsPagesFrom.encodeOverflowIndexTableGroups source
                  tableEncoding.nextPage database.tables indexEncodings
                  indexResult indexReads
              have indexRange : ∀ encoding ∈ indexEncodings,
                  tableEncoding.nextPage ≤ encoding.rootPage ∧
                  encoding.rootPage + encoding.pages.length ≤
                    tableEncoding.nextPage + indexPages.length := by
                simpa [indexPages] using
                  CoreOverflow.encodeIndexTableGroups_member_range
                    tableEncoding.nextPage database.tables indexEncodings
                    indexResult
              have tableNextPositive : 0 < tableEncoding.nextPage := by
                rw [tableNext, stateNext]
                omega
              have indexPositive : ∀ encoding ∈ indexEncodings,
                  0 < encoding.rootPage := by
                intro encoding member
                have range := indexRange encoding member
                omega
              have endBound : tableEncoding.nextPage + indexPages.length =
                  remaining.length + 2 := by
                simp only [remaining, List.length_append]
                rw [tableNext, stateNext, treeLength]
                omega
              have indexPageBound : ∀ encoding ∈ indexEncodings,
                  encoding.rootPage + encoding.pages.length < 2 ^ 32 := by
                intro encoding member
                have range := indexRange encoding member
                rw [endBound] at range
                change 1 + remaining.length + 1 < 2 ^ 32 at countBound
                omega
              have indexSourceBound : ∀ encoding ∈ indexEncodings,
                  encoding.rootPage + encoding.pages.length ≤
                    source.pageCount + 1 := by
                intro encoding member
                have range := indexRange encoding member
                rw [endBound] at range
                omega
              have tableHeights : ∀ table ∈ state.tables,
                  table.tree.root.erase.height < source.pageCount + 1 := by
                intro table member
                have height :=
                  RecursiveBPlusTree.Node.height_lt_pageCount
                    table.tree.root.erase
                have pageCount := PersistentPageTree.Node.pageIds_length
                  table.tree.root
                have included :=
                  CoreChunkPageState.TableState.pageIds_length_le_tablePageIds
                    member
                unfold CoreChunkPageState.TableState.pageIds at included
                rw [statePages] at included
                simp only [List.length_range'] at included
                omega
              have tablesDecoded :=
                decodeTablesFrom_encodeChunkTablesWithOverflow source
                  state.nextPage state.tables tableEncoding tableResult
                  treeContains overflowReads (by rw [stateNext]; omega)
                  (by
                    rw [stateNext]
                    change 1 + remaining.length + 1 < 2 ^ 32 at countBound
                    simp only [remaining, List.length_append, List.length_map]
                      at countBound
                    omega)
                  (by omega) tableHeights
              have safe : ∀ entry ∈ entries,
                  CoreDecode.CatalogTextRoundtrips entry := by
                intro entry _
                exact ⟨utf8 entry.kind, utf8 entry.name,
                  utf8 entry.table, utf8 entry.sql⟩
              have catalogDecoded :=
                CoreDecode.decodeCatalogForOpen_schemaPageForEntries
                  entries count safe schemaResult
              have tableFilter :
                  ((entries.map CoreDecode.CatalogEntry.ofEncoded).filter
                    (fun entry => entry.kind == "table")) =
                    tableEntries.map CoreDecode.CatalogEntry.ofEncoded := by
                rw [show entries.map CoreDecode.CatalogEntry.ofEncoded =
                    tableEntries.map CoreDecode.CatalogEntry.ofEncoded ++
                      indexEntries.map CoreDecode.CatalogEntry.ofEncoded by
                  simp [entries]]
                rw [List.filter_append]
                have tablesKept :
                    (tableEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                      (fun entry => entry.kind == "table") =
                        tableEntries.map CoreDecode.CatalogEntry.ofEncoded := by
                  apply List.filter_eq_self.mpr
                  intro entry member
                  rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember,
                    rfl⟩
                  rcases List.mem_map.mp encodedMember with ⟨table, _, rfl⟩
                  rfl
                have indexesRemoved :
                    (indexEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                      (fun entry => entry.kind == "table") = [] := by
                  apply List.filter_eq_nil_iff.mpr
                  intro entry member
                  rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember,
                    rfl⟩
                  rcases List.mem_map.mp encodedMember with ⟨encoding, _, rfl⟩
                  simp [CoreOverflow.IndexEncoding.catalogEntry,
                    CoreDecode.CatalogEntry.ofEncoded]
                rw [tablesKept, indexesRemoved, List.append_nil]
              have indexFilter :
                  ((entries.map CoreDecode.CatalogEntry.ofEncoded).filter
                    (fun entry => entry.kind == "index")) =
                    indexEntries.map CoreDecode.CatalogEntry.ofEncoded := by
                rw [show entries.map CoreDecode.CatalogEntry.ofEncoded =
                    tableEntries.map CoreDecode.CatalogEntry.ofEncoded ++
                      indexEntries.map CoreDecode.CatalogEntry.ofEncoded by
                  simp [entries]]
                rw [List.filter_append]
                have tablesRemoved :
                    (tableEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                      (fun entry => entry.kind == "index") = [] := by
                  apply List.filter_eq_nil_iff.mpr
                  intro entry member
                  rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember,
                    rfl⟩
                  rcases List.mem_map.mp encodedMember with ⟨table, _, rfl⟩
                  simp [chunkTableCatalogEntry,
                    CoreDecode.CatalogEntry.ofEncoded]
                have indexesKept :
                    (indexEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                      (fun entry => entry.kind == "index") =
                        indexEntries.map CoreDecode.CatalogEntry.ofEncoded := by
                  apply List.filter_eq_self.mpr
                  intro entry member
                  rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember,
                    rfl⟩
                  rcases List.mem_map.mp encodedMember with ⟨encoding, _, rfl⟩
                  rfl
                rw [tablesRemoved, indexesKept, List.nil_append]
              have tableList :
                  state.tables.map (fun table => table.table.withoutIndexes) =
                    database.tables.map Core.Table.withoutIndexes := by
                have stateTables :=
                  (CoreChunkPageState.State.build?_represents stateResult).2.1
                rw [← stateTables]
                simp [List.map_map, Function.comp_def]
              have tablesDecoded' :
                  (tableEntries.map CoreDecode.CatalogEntry.ofEncoded).mapM
                      (CoreDecode.decodeTableFrom source) =
                    some (database.tables.map Core.Table.withoutIndexes) := by
                unfold tableEntries
                simpa [List.map_map, Function.comp_def, tableList]
                  using tablesDecoded
              have indexesApplied :=
                CoreDecode.applyIndexesForOpen_overflowEncoded source database
                  tableEncoding.nextPage indexEncodings indexResult
                  individualIndexReads indexPositive indexPageBound
                  indexSourceBound
              have indexesApplied' :
                  CoreDecode.applyIndexesForOpen source database.withoutIndexes
                    (indexEntries.map CoreDecode.CatalogEntry.ofEncoded) =
                      some database.canonicalize := by
                simpa [indexEntries, CoreOverflow.indexEntriesOf,
                  List.map_map, Function.comp_def] using indexesApplied
              have canonicalFirstRead :
                  (CoreDecode.PageSource.ofList
                    ((schemaPage :: remaining).map CoreFile.Page.bytes)).readPage
                      1 = some schemaPage.bytes := by
                simp [CoreDecode.PageSource.ofList, CoreDecode.page?]
              refine .intro (entries.map CoreDecode.CatalogEntry.ofEncoded)
                ?_ ?_ ?_
              · rw [catalogRead, canonicalFirstRead]
                simp only [Option.bind_eq_bind, Option.bind]
                exact catalogDecoded
              · rw [tableFilter]
                exact tablesDecoded'
              · rw [indexFilter]
                exact indexesApplied'
          next => contradiction

theorem decodeFromPageSource_encodeBulk_in (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : encodeBulk database = some image)
    (source : CoreDecode.PageSource)
    (catalogRead :
      source.readPage 1 >>= CoreDecode.decodeCatalogForOpen =
        (CoreDecode.PageSource.ofList
          (image.pages.map CoreFile.Page.bytes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen)
    (activeTailReads : CoreDecode.ReadsPagesFrom source 2 image.pages.tail)
    (enoughPages : image.pageCount ≤ source.pageCount) :
    CoreDecode.decodeFromPageSource source = some database.canonicalize :=
  (pageSourceRepresents_encodeBulk_in utf8 database image encoded source
    catalogRead activeTailReads enoughPages).decode

theorem decodeFromPageSource_encodeBulk (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : encodeBulk database = some image) :
    CoreDecode.decodeFromPageSource
      (.ofList (image.pages.map CoreFile.Page.bytes)) =
        some database.canonicalize := by
  apply decodeFromPageSource_encodeBulk_in utf8 database image encoded
  · rfl
  · exact CoreDecode.ReadsPagesFrom.ofList_tail image.pages
  · simp [CoreDecode.PageSource.ofList, CoreFile.Image.pageCount]

/-- The live bulk encoder persists the generated-image provenance stamp in
the bytes that a cold reader actually parses. -/
theorem encodeBulk_generatedHeader {database : Core.Database}
    {image : CoreFile.Image} (encoded : encodeBulk database = some image) :
    ∃ header suffix,
      FileFormat.decodeDatabaseHeader image.fileBytes = some (header, suffix) ∧
      CoreFile.GeneratedImageHeader header := by
  rcases encodeBulk_header encoded with
    ⟨count, schema, remaining, body, pagesEqual, _, headerEqual⟩
  refine ⟨CoreFile.databaseHeader count,
    body ++ remaining.flatMap CoreFile.Page.bytes, ?_,
    CoreFile.databaseHeader_generatedImage count⟩
  unfold CoreFile.Image.fileBytes
  rw [pagesEqual]
  simp only [List.flatMap_cons]
  rw [headerEqual]
  simpa [List.append_assoc] using
    FileFormat.decodeDatabaseHeader_encode (CoreFile.databaseHeader count)
      (body ++ remaining.flatMap CoreFile.Page.bytes)

theorem decode_encodeBulk (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : encodeBulk database = some image) :
    CoreDecode.decode image.fileBytes = some database.canonicalize := by
  rcases encodeBulk_header encoded with
    ⟨count, schema, remaining, body, pagesEqual, countEqual, headerEqual⟩
  have bytesLayout : image.fileBytes =
      FileFormat.encodeDatabaseHeader (CoreFile.databaseHeader count) ++
        (body ++ remaining.flatMap CoreFile.Page.bytes) := by
    unfold CoreFile.Image.fileBytes
    rw [pagesEqual]
    simp only [List.flatMap_cons]
    rw [headerEqual]
    simp [List.append_assoc]
  have fileLength : image.fileBytes.length =
      count.val * PhysicalCodec.pageSize := by
    rw [CoreFile.Image.fileBytes_length, countEqual, Nat.mul_comm]
  have splitPages : CoreDecode.pages count.val image.fileBytes =
      image.pages.map CoreFile.Page.bytes := by
    rw [← countEqual]
    exact CoreDecode.pages_image image
  unfold CoreDecode.decode
  rw [bytesLayout, FileFormat.decodeDatabaseHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show (CoreFile.databaseHeader count).databaseSizePages.val = count.val
    from rfl]
  rw [dif_pos (by rfl), dif_pos (by rfl), dif_pos (by rfl)]
  rw [← bytesLayout]
  rw [dif_pos fileLength, splitPages]
  exact decodeFromPageSource_encodeBulk utf8 database image encoded

/-- Compatibility name retained for adapters.  The former runtime decode and
whole-database comparison has been discharged by `decode_encodeBulk`; emitted
bytes now come directly from the proved bulk encoder. -/
def encodeChecked (database : Core.Database) : Option CoreFile.Image :=
  encodeBulk database

theorem decode_encodeChecked (utf8 : CoreDecode.UTF8Roundtrips)
    {database : Core.Database} {image : CoreFile.Image}
    (encoded : encodeChecked database = some image) :
    ∃ decoded, CoreDecode.decode image.fileBytes = some decoded ∧
      decoded.Equiv database := by
  unfold encodeChecked at encoded
  exact ⟨database.canonicalize,
    decode_encodeBulk utf8 database image encoded,
    database.canonicalize_equiv⟩

end CorePageCodec
end SQLeanite
