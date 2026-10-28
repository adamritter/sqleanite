import SQLeanite.CoreChunkPageState.Chunk
import SQLeanite.CoreDecode.LookupIndexValueFromEncodeIndexExact

namespace SQLeanite
namespace CorePageCodec

structure NumberedPage where
  pageNumber : Nat
  page : CoreFile.Page

def encodeLeaf (schema : Core.Schema)
    (entries : List (PagedBTree.Entry Core.Row)) : Option CoreFile.Page := do
  let cells ← entries.mapM fun entry => CoreRecord.encodeCell? schema entry.2
  CoreFile.tableLeafPage? cells

theorem mapM_map_entry_values
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

def findRowid (target : Core.Integer) (rows : List Core.Row) :
    Option Core.Row :=
  rows.find? fun row => row.rowid = target

/-- In a globally ordered row sequence, the greatest rowid of the left side
is an exact routing separator.  This is the logical fact used by both physical
interior-page shapes. -/
theorem findRowid_append_routed (target boundary : Core.Integer)
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

theorem rowid_le_of_pairwise_last
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
          exact CoreDecode.canonicalPointersBeginAtContent_leafPageBody cells fits

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

inductive PhysicalChunkPage where
  | leaf (pageNumber : Nat)
      (entries : List (PagedBTree.Entry CoreChunkPageState.Chunk))
  | branch2 (pageNumber leftPage : Nat) (leftKey : Option Nat)
      (rightPage : Nat)
  | branch3 (pageNumber leftPage : Nat) (leftKey : Option Nat)
      (middlePage : Nat) (middleKey : Option Nat) (rightPage : Nat)
  deriving DecidableEq

def PhysicalChunkPage.pageNumber : PhysicalChunkPage → Nat
  | .leaf pageNumber _ | .branch2 pageNumber .. | .branch3 pageNumber .. =>
      pageNumber

/-- Preorder physical descriptors retain the same stable page identities as
the persistent tree while making byte-level dependencies explicit. -/
def physicalChunkPages :
    PersistentPageTree.Node CoreChunkPageState.Chunk →
      List PhysicalChunkPage
  | .leaf pageId entries => [.leaf pageId entries]
  | .branch2 pageId left _ right =>
      .branch2 pageId left.rootId (maximumChunkRowid? left) right.rootId ::
        physicalChunkPages left ++ physicalChunkPages right
  | .branch3 pageId left _ middle _ right =>
      .branch3 pageId left.rootId (maximumChunkRowid? left) middle.rootId
          (maximumChunkRowid? middle) right.rootId ::
        physicalChunkPages left ++ physicalChunkPages middle ++
          physicalChunkPages right

def physicalChunkRoot :
    PersistentPageTree.Node CoreChunkPageState.Chunk → PhysicalChunkPage
  | .leaf pageId entries => .leaf pageId entries
  | .branch2 pageId left _ right =>
      .branch2 pageId left.rootId (maximumChunkRowid? left) right.rootId
  | .branch3 pageId left _ middle _ right =>
      .branch3 pageId left.rootId (maximumChunkRowid? left) middle.rootId
        (maximumChunkRowid? middle) right.rootId

def physicalChunkPath (key : Nat) :
    PersistentPageTree.Node CoreChunkPageState.Chunk →
      List PhysicalChunkPage
  | node@(.leaf ..) => [physicalChunkRoot node]
  | node@(.branch2 _ left separator right) =>
      physicalChunkRoot node ::
        if key < separator then physicalChunkPath key left
        else physicalChunkPath key right
  | node@(.branch3 _ left firstSeparator middle secondSeparator right) =>
      physicalChunkRoot node ::
        if key < firstSeparator then physicalChunkPath key left
        else if key < secondSeparator then physicalChunkPath key middle
        else physicalChunkPath key right

/-- One-pass cache for the descriptor traversal.  The last logical entry is
enough to derive a subtree's physical separator, so parent construction need
not repeatedly flatten descendant rows. -/
structure PhysicalChunkSummary where
  pages : List PhysicalChunkPage
  lastEntry? : Option (PagedBTree.Entry CoreChunkPageState.Chunk)

def PhysicalChunkSummary.maximumRowid? (summary : PhysicalChunkSummary) :
    Option Nat :=
  summary.lastEntry?.bind fun entry =>
    entry.2.getLast?.map (fun row => row.rowid.toUnsigned)

def summarizePhysicalChunkPages :
    PersistentPageTree.Node CoreChunkPageState.Chunk → PhysicalChunkSummary
  | .leaf pageId entries => ⟨[.leaf pageId entries], entries.getLast?⟩
  | .branch2 pageId left _ right =>
      let leftSummary := summarizePhysicalChunkPages left
      let rightSummary := summarizePhysicalChunkPages right
      ⟨.branch2 pageId left.rootId leftSummary.maximumRowid? right.rootId ::
          leftSummary.pages ++ rightSummary.pages,
        rightSummary.lastEntry?.or leftSummary.lastEntry?⟩
  | .branch3 pageId left _ middle _ right =>
      let leftSummary := summarizePhysicalChunkPages left
      let middleSummary := summarizePhysicalChunkPages middle
      let rightSummary := summarizePhysicalChunkPages right
      ⟨.branch3 pageId left.rootId leftSummary.maximumRowid? middle.rootId
            middleSummary.maximumRowid? right.rootId ::
          leftSummary.pages ++ middleSummary.pages ++ rightSummary.pages,
        rightSummary.lastEntry?.or
          (middleSummary.lastEntry?.or leftSummary.lastEntry?)⟩

theorem summarizePhysicalChunkPages_lastEntry (node :
    PersistentPageTree.Node CoreChunkPageState.Chunk) :
    (summarizePhysicalChunkPages node).lastEntry? =
      node.erase.toList.getLast? := by
  induction node with
  | leaf pageId entries => rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp [summarizePhysicalChunkPages, PersistentPageTree.Node.erase,
        RecursiveBPlusTree.Node.toList, List.getLast?_append,
        leftInduction, rightInduction]
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp [summarizePhysicalChunkPages, PersistentPageTree.Node.erase,
        RecursiveBPlusTree.Node.toList, List.getLast?_append,
        leftInduction, middleInduction, rightInduction, List.append_assoc,
        Option.or_assoc]

theorem summarizePhysicalChunkPages_maximum (node :
    PersistentPageTree.Node CoreChunkPageState.Chunk) :
    (summarizePhysicalChunkPages node).maximumRowid? =
      maximumChunkRowid? node := by
  unfold PhysicalChunkSummary.maximumRowid? maximumChunkRowid?
  rw [summarizePhysicalChunkPages_lastEntry]

def physicalChunkPagesFast (node :
    PersistentPageTree.Node CoreChunkPageState.Chunk) :
    List PhysicalChunkPage :=
  (summarizePhysicalChunkPages node).pages

end CorePageCodec

end SQLeanite
