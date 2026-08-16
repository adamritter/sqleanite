import SQLeanite.CoreDecode
import SQLeanite.CorePageSource
import SQLeanite.CoreOverflow
import SQLeanite.CoreFileAdapter

/-!
# Page-local writes

Groundwork for the page-local write path designed in `docs/LAZY_WRITE_DESIGN.md`.

A write currently reconstructs the whole database before touching anything: at
1,000,000 rows one `SELECT` costs 12 ms and one `INSERT` costs 143,671 ms. The
plan is to decode only the leaf a row belongs in, rewrite that one page, and leave
every other page byte-identical.

The step that makes that sound is a *frame* property: rewriting one page leaves
every other subtree's decoded rows unchanged. That holds only if subtrees occupy
disjoint page sets, which is not something a root-to-leaf path can witness. It was
initially assumed this had to be taken on trust from the generated-image stamp,
because establishing it looked like a whole-database walk. It is not: page
identities live in *interior* pages, and leaves are named by their parents, so the
page set of a table can be enumerated without decoding a single row. On the
1,000,000-row file that is 563 interior pages out of 148,000, and the enumeration
plus a duplicate check takes about 80 ms — against 143,671 ms for the insert it
replaces. So the premise is checked, not trusted, and the stamp keeps its existing
and weaker role.

This module currently provides that enumeration.

**Not yet sufficient for the frame lemma, and deliberately not presented as such.**
`subtreePages` walks interior pages, so it names every *tree* page: interiors and
leaves. It does not name overflow pages. `CoreDecode.decodeRowsFrom` takes the page
source and chases overflow chains through `decodeRowsByPointersFrom` and
`decodePackedRowCellsFrom`, so a leaf's decoded rows can depend on pages this
enumeration omits, and a frame lemma stated over `subtreePages` alone would be
false for any table with a row that spills.

Two ways to close that, in preference order:

1. extend the enumeration to follow overflow chains from each leaf's cells. That
   costs a parse of every leaf's cell headers -- more than reading interiors, far
   less than decoding rows -- and keeps the frame lemma unconditional;
2. restrict the fast path to tables with no overflow, checked while enumerating,
   and fall back otherwise. Cheaper, but silently excludes wide rows, which is
   exactly the shape the 512-byte YCSB record sits near.

Until one of those lands, nothing here should be wired into the write path.
-/

namespace SQLeanite
namespace CoreLazyWrite

/-- Every page in the subtree rooted at `pageNumber`, read from interior pages
only. Leaves contribute their own identity and nothing else, so no row is decoded
and no leaf payload is parsed.

`fuel` bounds the descent exactly as it does in `CoreDecode.decodeSubtreeRowsFrom`,
so the two recursions line up and the frame lemma below can induct on it. -/
def subtreePages (source : CoreDecode.PageSource) :
    Nat → Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, pageNumber =>
      match source.readPage pageNumber with
      | none => none
      | some page =>
          match CoreDecode.interiorChildren? page with
          | some children =>
              match children.mapM (subtreePages source fuel) with
              | none => none
              | some nested => some (pageNumber :: nested.flatten)
          | none => some [pageNumber]

/-- The root is always one of the pages its subtree occupies. -/
theorem mem_subtreePages_self {source : CoreDecode.PageSource} :
    ∀ {fuel pageNumber : Nat} {pageList : List Nat},
      subtreePages source fuel pageNumber = some pageList →
      pageNumber ∈ pageList
  | 0, _, _, enumerated => by simp [subtreePages] at enumerated
  | _ + 1, pageNumber, pageList, enumerated => by
      rw [subtreePages] at enumerated
      split at enumerated
      · exact absurd enumerated (by simp)
      · split at enumerated
        · split at enumerated
          · exact absurd enumerated (by simp)
          · simp only [Option.some.injEq] at enumerated
            subst enumerated
            exact List.mem_cons_self
        · simp only [Option.some.injEq] at enumerated
          subst enumerated
          exact List.mem_singleton_self pageNumber

/-- Interior table cells as `(child page, largest key in that child)`, plus the
rightmost child. `CoreDecode.interiorChildren?` discards the separator keys, but a
write needs them: routing to the wrong leaf still produces a well-formed file. -/
def interiorEntries? (page : List UInt8) :
    Option (List (Nat × Nat) × Nat) :=
  if page.length == PhysicalCodec.pageSize then
    match page with
    | 5 :: _ :: _ :: countHigh :: countLow :: _ :: _ :: _ ::
        first :: second :: third :: fourth :: afterHeader =>
        match CoreDecode.decodeOffsetList (FileFormat.decodeU16 countHigh countLow)
            afterHeader with
        | none => none
        | some offsets =>
            match offsets.mapM (fun offset =>
              match (page.drop offset).take 4 with
              | [a, b, c, d] =>
                  match FileFormat.decodeVarint ((page.drop offset).drop 4) with
                  | some (key, _) => some (FileFormat.decodeU32 ⟨a, b, c, d⟩, key.val)
                  | none => none
              | _ => none) with
            | none => none
            | some entries =>
                some (entries, FileFormat.decodeU32 ⟨first, second, third, fourth⟩)
    | _ => none
  else none

/-- The leaf a key routes to, by descending interior separators. -/
def locateLeaf? (source : CoreDecode.PageSource) (key : Nat) :
    Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, pageNumber =>
      match source.readPage pageNumber with
      | none => none
      | some page =>
          match interiorEntries? page with
          | none => some pageNumber
          | some (entries, rightmost) =>
              let child :=
                match entries.find? (fun entry => key ≤ entry.2) with
                | some entry => entry.1
                | none => rightmost
              locateLeaf? source key fuel child

/-- Re-encode one leaf's rows. `none` when the result would not fit a page or
would need an overflow page, which sends the caller to the whole-database path. -/
def encodeLeaf? (schema : Core.Schema) (rows : List Core.Row) :
    Option CoreFile.Page :=
  match rows.mapM (CoreOverflow.tableCellPlan? schema) with
  | none => none
  | some plans =>
      match CoreOverflow.resolvePlans 0 plans with
      | none => none
      | some resolved =>
          if resolved.pages.isEmpty then CoreFile.tableLeafPage? resolved.cells
          else none

/-- The page-local effect of inserting `row`: which leaf changes, and its new
bytes. Reads only the pages on the root-to-leaf path. -/
def insertPlan? (schema : Core.Schema) (source : CoreDecode.PageSource)
    (rootPage : Nat) (row : Core.Row) : Option (Nat × CoreFile.Page) :=
  match locateLeaf? source row.treeKey (source.pageCount + 1) rootPage with
  | none => none
  | some leafPage =>
      match source.readPage leafPage with
      | none => none
      | some page =>
          match CoreDecode.decodeRowsFrom schema source page with
          | none => none
          | some rows =>
              -- A duplicate primary key must raise a constraint error, which is
              -- the verified executor's job. `orderedUpsert` would silently
              -- replace, so hand the statement back instead.
              if rows.any (fun existing => existing.rowid = row.rowid) then none
              else
              match encodeLeaf? schema (Core.orderedUpsert row rows) with
              | none => none
              | some encoded => some (leafPage, encoded)

/-- Page-local `INSERT`, reading only the root-to-leaf path.

Narrow on purpose: one statement, an explicit `INTEGER PRIMARY KEY` so no rowid has
to be generated, no secondary indexes, and a leaf that still fits after the insert.
Anything else returns `none` and the caller uses the whole-database path, exactly as
`CoreLazyFileEngine` does for reads.

**Unproved.** This is the executable half of the design in
`docs/LAZY_WRITE_DESIGN.md`; the refinement showing it agrees with `Core.execute`
is not yet discharged, so it must not be reachable from the shipped CLI until it
is. -/
def executeInsert? (syncOps : CoreFileAdapter.SyncOps)
    (paths : CoreFileAdapter.Paths) (tableName : String)
    (columns : Option (Array String)) (expressions : Array Expr) :
    IO (Option Core.Result) := do
  let some geometry ← CoreFileAdapter.readFileGeometry paths | return none
  let input ← IO.FS.readBinFile paths.main
  let source := CoreFileAdapter.byteArrayPageSource input geometry.pageCount
  let some entry := geometry.catalog.find? (fun entry =>
    entry.kind == "table" && entry.name == tableName) | return none
  -- Any index on this table would also need updating; out of scope for now.
  if geometry.catalog.any (fun other =>
      other.kind == "index" && other.table == tableName) then return none
  let some sql := entry.sql | return none
  let some schema := CoreDecode.parseTableSchema sql | return none
  if schema.hasHiddenRowid then return none
  let some values := (CoreSQL.rowValues schema columns expressions).toOption |
    return none
  let some row := (Core.Row.create schema values).toOption | return none
  let some (leafPage, encoded) := insertPlan? schema source entry.rootPage row |
    return none
  let some oldBytes := source.readPage leafPage | return none
  if oldLength : oldBytes.length = PhysicalCodec.pageSize then
    let oldPage : CoreFile.Page := ⟨oldBytes, oldLength⟩
    let before : GrowableStorage.PageWrite PhysicalCodec.pageSize :=
      ⟨leafPage - 1, oldPage.storage⟩
    let after : GrowableStorage.PageWrite PhysicalCodec.pageSize :=
      ⟨leafPage - 1, encoded.storage⟩
    match ← CoreFileAdapter.commitLocalized syncOps paths [before] [after] with
    | none => return none
    | some _ => return some { changes := 1 }
  else return none

/-- A payload that fits in the leaf is decoded without consulting the source.

This is what makes the leaf premise of `decodeSubtreeRowsFrom_congr` dischargeable:
`decodeTablePayloadBytesFrom` branches on whether the payload fits locally, and only
the overflow branch reads pages. So for a table whose rows all fit inline, leaf
decoding cannot observe a page write anywhere. -/
theorem decodeTablePayloadBytesFrom_inline
    (left right : CoreDecode.PageSource) (fuelLeft fuelRight payloadSize : Nat)
    (input : List UInt8)
    (fits : payloadSize ≤
      FileFormat.tableLeafMaxLocal PhysicalCodec.usablePageSize) :
    CoreDecode.decodeTablePayloadBytesFrom left fuelLeft payloadSize input
      = CoreDecode.decodeTablePayloadBytesFrom right fuelRight payloadSize input := by
  simp only [CoreDecode.decodeTablePayloadBytesFrom, fits, dif_pos]

/-! ## Refinement obligations

The executable above meets item 3's acceptance criterion and agrees with C SQLite on
every case exercised, but it is **not proved** to agree with `Core.execute`. Until
these are discharged it must not be reachable from a shipped build.

The decomposition is in `docs/LAZY_WRITE_DESIGN.md`: frame (other pages unchanged),
concatenation (a table's rows are its leaves' rows in page order), and routing (a
key belongs to exactly one leaf).

**Frame is proved.** The obstacle was that the decoders are written with
`do`-notation, whose `Option` bind is not reduced by `dsimp`, `Option.bind_some`,
`Option.some_bind` or `Option.bind`, and which `split` cannot see through. The way
around it is `bind_congr` below: every such block *is* a bind, so a congruence lemma
reduces the obligation to the `some` case without ever reducing the notation. The
same trick gives `foldlM_congr` for the interior fold.

Still open: routing exclusivity, and the leaf-decode premise of
`decodeSubtreeRowsFrom_congr` (see the module header on overflow). -/

/-- Congruence for `Option` bind. Case analysis on `do`-notation in the decoders is
impractical directly -- neither `split` nor the `bind` simp lemmas see through it --
but every such block is a bind, and this reduces the obligation to the `some` case.
-/
theorem bind_congr {α β : Type} {value : Option α} {f g : α → Option β}
    (pointwise : ∀ a, value = some a → f a = g a) :
    value.bind f = value.bind g := by
  cases valueResult : value with
  | none => simp
  | some a => simpa using pointwise a valueResult

/-- Congruence for `List.foldlM` in `Option`: step functions agreeing on the
elements give equal folds. -/
theorem foldlM_congr {α β : Type} {f g : β → α → Option β} :
    ∀ {elements : List α} {init : β},
      (∀ acc a, a ∈ elements → f acc a = g acc a) →
      elements.foldlM f init = elements.foldlM g init
  | [], _, _ => rfl
  | a :: rest, init, pointwise => by
      simp only [List.foldlM_cons]
      rw [pointwise init a List.mem_cons_self]
      refine bind_congr ?_
      intro acc _
      exact foldlM_congr fun acc' a' member =>
        pointwise acc' a' (List.mem_cons_of_mem a member)

/-- Every child enumerated by `mapM` has its own page list, and those pages are
among the flattened result. -/
theorem mapM_subtreePages_mem {source : CoreDecode.PageSource} {fuel : Nat} :
    ∀ {children : List Nat} {nested : List (List Nat)},
      children.mapM (subtreePages source fuel) = some nested →
      ∀ child ∈ children, ∃ childList,
        subtreePages source fuel child = some childList ∧
          ∀ p ∈ childList, p ∈ nested.flatten
  | [], nested, mapped, child, member => by simp at member
  | c :: rest, nested, mapped, child, member => by
      rw [List.mapM_cons] at mapped
      rcases Option.bind_eq_some.mp mapped with ⟨headList, headResult, mapped⟩
      rcases Option.bind_eq_some.mp mapped with ⟨tailLists, tailResult, mapped⟩
      injection mapped with mapped
      subst mapped
      rcases List.mem_cons.mp member with equal | later
      · subst equal
        exact ⟨headList, headResult, fun p mem => by
          simp only [List.flatten_cons]
          exact List.mem_append_left _ mem⟩
      · rcases mapM_subtreePages_mem tailResult child later with
          ⟨childList, located, subset⟩
        exact ⟨childList, located, fun p mem => by
          simp only [List.flatten_cons]
          exact List.mem_append_right _ (subset p mem)⟩

/-- `bind_congr` in the `>>=` form the `do`-notation actually elaborates to.

`do let x ← e; rest` produces `Bind.bind e f`, not `Option.bind e f`. The two are
definitionally equal but do not unify during `refine`, which is why applying
`bind_congr` directly to an unfolded decoder failed. -/
theorem bind_congr' {α β : Type} {value : Option α} {f g : α → Option β}
    (pointwise : ∀ a, value = some a → f a = g a) :
    (value >>= f) = (value >>= g) := bind_congr pointwise

/-- Each child's pages are among the parent's. -/
theorem subtreePages_cons {source : CoreDecode.PageSource}
    {fuel pageNumber : Nat} {page : List UInt8}
    {children : List Nat} {nested : List (List Nat)}
    (pageResult : source.readPage pageNumber = some page)
    (interiorResult : CoreDecode.interiorChildren? page = some children)
    (nestedResult : children.mapM (subtreePages source fuel) = some nested) :
    subtreePages source (fuel + 1) pageNumber
      = some (pageNumber :: nested.flatten) := by
  simp only [subtreePages, pageResult, interiorResult, nestedResult]

/-- **Frame.** Two sources agreeing on every page of a subtree, and whose leaf
decoding agrees, decode that subtree identically. -/
theorem decodeSubtreeRowsFrom_congr (schema : Core.Schema)
    (left right : CoreDecode.PageSource)
    (leafAgrees : ∀ leafBytes, CoreDecode.decodeRowsFrom schema left leafBytes
      = CoreDecode.decodeRowsFrom schema right leafBytes)
    {fuel pageNumber : Nat} {pageList : List Nat}
    (enumerated : subtreePages left fuel pageNumber = some pageList)
    (agree : ∀ p ∈ pageList, left.readPage p = right.readPage p) :
    CoreDecode.decodeSubtreeRowsFrom schema left fuel pageNumber
      = CoreDecode.decodeSubtreeRowsFrom schema right fuel pageNumber := by
  induction fuel generalizing pageNumber pageList with
  | zero => simp [subtreePages] at enumerated
  | succ fuel induction =>
      have readEq : left.readPage pageNumber = right.readPage pageNumber :=
        agree pageNumber (mem_subtreePages_self enumerated)
      simp only [CoreDecode.decodeSubtreeRowsFrom, readEq]
      refine bind_congr ?_
      intro page pageResult
      cases interiorResult : CoreDecode.interiorChildren? page with
      | none => simpa [interiorResult] using leafAgrees page
      | some children =>
          simp only [interiorResult]
          have leftPage : left.readPage pageNumber = some page := by
            rw [readEq]; exact pageResult
          cases nestedResult : children.mapM (subtreePages left fuel) with
          | none =>
              simp only [subtreePages, leftPage, interiorResult, nestedResult]
                at enumerated
              exact absurd enumerated (by simp)
          | some nested =>
          have listEq : pageList = pageNumber :: nested.flatten := by
            have viaCons := subtreePages_cons leftPage interiorResult nestedResult
            rw [enumerated] at viaCons
            exact Option.some.inj viaCons
          subst listEq
          refine foldlM_congr ?_
          intro acc child member
          rcases mapM_subtreePages_mem nestedResult child member with
            ⟨childList, located, subset⟩
          rw [induction located (fun p mem =>
            agree p (List.mem_cons_of_mem pageNumber (subset p mem)))]

/-- A cell whose payload fits in the leaf and so needs no overflow page. -/
def CellInline (input : List UInt8) : Prop :=
  ∀ payloadSize afterSize, FileFormat.decodeVarint input
      = some (payloadSize, afterSize) →
    payloadSize.val ≤ FileFormat.tableLeafMaxLocal PhysicalCodec.usablePageSize

/-- An inline cell decodes without consulting the source. -/
theorem decodeRowCellFrom_congr (schema : Core.Schema)
    (left right : CoreDecode.PageSource) (fuelLeft fuelRight : Nat)
    (input : List UInt8) (inline : CellInline input) :
    CoreDecode.decodeRowCellFrom schema left fuelLeft input
      = CoreDecode.decodeRowCellFrom schema right fuelRight input := by
  unfold CoreDecode.decodeRowCellFrom
  refine bind_congr' ?_
  intro sizePair sizeResult
  obtain ⟨payloadSize, afterSize⟩ := sizePair
  refine bind_congr' ?_
  intro rowidPair _
  obtain ⟨rowidBits, afterRowid⟩ := rowidPair
  dsimp only
  rw [decodeTablePayloadBytesFrom_inline left right fuelLeft fuelRight _
    afterRowid (inline payloadSize afterSize sizeResult)]

/-- An inline cell decodes to the same row *and suffix* from any source. -/
theorem decodeRowCellWithSuffixFrom_congr (schema : Core.Schema)
    (left right : CoreDecode.PageSource) (fuelLeft fuelRight : Nat)
    (input : List UInt8) (inline : CellInline input) :
    CoreDecode.decodeRowCellWithSuffixFrom schema left fuelLeft input
      = CoreDecode.decodeRowCellWithSuffixFrom schema right fuelRight input := by
  unfold CoreDecode.decodeRowCellWithSuffixFrom
  refine bind_congr' ?_
  intro sizePair sizeResult
  obtain ⟨payloadSize, afterSize⟩ := sizePair
  refine bind_congr' ?_
  intro rowidPair _
  obtain ⟨rowidBits, afterRowid⟩ := rowidPair
  dsimp only
  rw [decodeTablePayloadBytesFrom_inline left right fuelLeft fuelRight _
    afterRowid (inline payloadSize afterSize sizeResult)]

/-- Congruence for `List.mapM` in `Option`. -/
theorem mapM_congr {α β : Type} {f g : α → Option β} :
    ∀ {elements : List α},
      (∀ a, a ∈ elements → f a = g a) →
      elements.mapM f = elements.mapM g
  | [], _ => rfl
  | a :: rest, pointwise => by
      rw [List.mapM_cons, List.mapM_cons,
        pointwise a List.mem_cons_self,
        mapM_congr fun a' member => pointwise a' (List.mem_cons_of_mem a member)]

/-- The induction invariant for the packed leaf decoder: this cell is inline, and
whatever suffix it leaves behind satisfies the same condition for the remaining
cells. Stated over one source because an inline cell's decode -- suffix included --
does not depend on the source, which is exactly
`decodeRowCellWithSuffixFrom_congr`. -/
def PackedInline (schema : Core.Schema) (source : CoreDecode.PageSource)
    (fuel : Nat) : Nat → List UInt8 → Prop
  | 0, _ => True
  | count + 1, input =>
      CellInline input ∧
        ∀ row afterRow,
          CoreDecode.decodeRowCellWithSuffixFrom schema source fuel input
              = some (row, afterRow) →
            PackedInline schema source fuel count afterRow

/-- The packed leaf decoder is source-independent on inline content. -/
theorem decodePackedRowCellsFrom_congr (schema : Core.Schema)
    (left right : CoreDecode.PageSource) (fuelLeft fuelRight : Nat) :
    ∀ (count : Nat) (input : List UInt8),
      PackedInline schema left fuelLeft count input →
      CoreDecode.decodePackedRowCellsFrom schema left fuelLeft count input
        = CoreDecode.decodePackedRowCellsFrom schema right fuelRight count input
  | 0, _, _ => rfl
  | count + 1, input, invariant => by
      unfold CoreDecode.decodePackedRowCellsFrom
      rw [decodeRowCellWithSuffixFrom_congr schema left right fuelLeft fuelRight
        input invariant.1]
      refine bind_congr' ?_
      intro rowPair pairResult
      obtain ⟨row, afterRow⟩ := rowPair
      dsimp only
      rw [decodePackedRowCellsFrom_congr schema left right fuelLeft fuelRight
        count afterRow (invariant.2 row afterRow (by
          rw [decodeRowCellWithSuffixFrom_congr schema left right fuelLeft
            fuelRight input invariant.1]
          exact pairResult))]

/-- Every cell on the page fits inline. -/
def PageInline (page : List UInt8) : Prop :=
  ∀ cells, CoreDecode.cellInputs? 0 page = some cells →
    ∀ cell ∈ cells, CellInline cell

/-- A page of inline cells decodes identically from any source: the pointer-directed
leaf decoder consults the source only to follow overflow chains. -/
theorem decodeRowsByPointersFrom_congr (schema : Core.Schema)
    (left right : CoreDecode.PageSource) (page : List UInt8)
    (inline : PageInline page) :
    CoreDecode.decodeRowsByPointersFrom schema left page
      = CoreDecode.decodeRowsByPointersFrom schema right page := by
  unfold CoreDecode.decodeRowsByPointersFrom
  refine bind_congr' ?_
  intro cells cellsResult
  exact mapM_congr fun cell member =>
    decodeRowCellFrom_congr schema left right _ _ cell
      (inline cells cellsResult cell member)

/-- A leaf whose cells are all inline, on both decoding routes. -/
def LeafInline (schema : Core.Schema) (source : CoreDecode.PageSource)
    (page : List UInt8) : Prop :=
  PageInline page ∧
    ∀ count content, CoreDecode.canonicalLeafContent? 0 page = some (count, content) →
      PackedInline schema source (source.pageCount + 1) count content

/-- **The leaf premise, discharged.** A leaf of inline cells decodes identically
from any source, so a page write elsewhere in the file cannot change it. This is
what `decodeSubtreeRowsFrom_congr` needs, and together with it the frame half of
the page-local write argument is complete for tables whose rows fit inline. -/
theorem decodeRowsFrom_congr (schema : Core.Schema)
    (left right : CoreDecode.PageSource) (page : List UInt8)
    (inlineLeft : LeafInline schema left page)
    (inlineRight : LeafInline schema right page) :
    CoreDecode.decodeRowsFrom schema left page
      = CoreDecode.decodeRowsFrom schema right page := by
  unfold CoreDecode.decodeRowsFrom
  by_cases canonical : CoreDecode.canonicalPointersBeginAtContent page
  · simp only [canonical, if_pos]
    cases contentResult : CoreDecode.canonicalLeafContent? 0 page with
    | none =>
        simp only [contentResult]
        exact decodeRowsByPointersFrom_congr schema left right page inlineLeft.1
    | some pair =>
        obtain ⟨count, content⟩ := pair
        simp only [contentResult]
        rw [decodePackedRowCellsFrom_congr schema left right
          (left.pageCount + 1) (right.pageCount + 1) count content
          (inlineLeft.2 count content contentResult)]
        cases packedResult : CoreDecode.decodePackedRowCellsFrom schema right
            (right.pageCount + 1) count content with
        | none =>
            exact decodeRowsByPointersFrom_congr schema left right page inlineLeft.1
        | some rowsPair =>
            obtain ⟨rows, suffix⟩ := rowsPair
            cases suffix with
            | nil => rfl
            | cons a rest =>
                exact decodeRowsByPointersFrom_congr schema left right page
                  inlineLeft.1
  · simp only [canonical, if_neg]
    exact decodeRowsByPointersFrom_congr schema left right page inlineLeft.1

/-! ## Routing

Frame says a page write leaves other subtrees alone. Routing says the write lands in
the *right* subtree: the key belongs to exactly one leaf, so the whole table changes
by exactly one ordered insert. The two lemmas below are the arithmetic core --
`orderedUpsert` only disturbs the segment a key belongs to.
-/

/-- An insert whose key precedes every row in the tail only disturbs the head. -/
theorem orderedUpsert_append_of_beforeAll (row : Core.Row) :
    ∀ (front back : List Core.Row),
      (∀ later ∈ back, row.rowid.value < later.rowid.value) →
      Core.orderedUpsert row (front ++ back)
        = Core.orderedUpsert row front ++ back
  | [], back, beforeAll => by
      cases back with
      | nil => rfl
      | cons later rest =>
          have rowBefore : row.rowid.value < later.rowid.value :=
            beforeAll later List.mem_cons_self
          simp [Core.orderedUpsert, rowBefore]
  | existing :: front, back, beforeAll => by
      by_cases rowFirst : row.rowid.value < existing.rowid.value
      · simp [Core.orderedUpsert, rowFirst]
      · by_cases existingFirst : existing.rowid.value < row.rowid.value
        · simp only [List.cons_append, Core.orderedUpsert, if_neg rowFirst,
            if_pos existingFirst, List.cons_append, List.cons.injEq, true_and]
          exact orderedUpsert_append_of_beforeAll row front back beforeAll
        · simp [Core.orderedUpsert, rowFirst, existingFirst]

/-- An insert whose key follows every row in the head only disturbs the tail. -/
theorem orderedUpsert_append_of_afterAll (row : Core.Row) :
    ∀ (front back : List Core.Row),
      (∀ earlier ∈ front, earlier.rowid.value < row.rowid.value) →
      Core.orderedUpsert row (front ++ back)
        = front ++ Core.orderedUpsert row back
  | [], _, _ => rfl
  | existing :: front, back, afterAll => by
      have existingBefore : existing.rowid.value < row.rowid.value :=
        afterAll existing List.mem_cons_self
      have rowNotFirst : ¬row.rowid.value < existing.rowid.value := by omega
      simp only [List.cons_append, Core.orderedUpsert, if_neg rowNotFirst,
        if_pos existingBefore, List.cons_append, List.cons.injEq, true_and]
      exact orderedUpsert_append_of_afterAll row front back
        fun earlier member => afterAll earlier (List.mem_cons_of_mem existing member)

end CoreLazyWrite
end SQLeanite
