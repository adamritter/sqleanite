import SQLeanite.CoreDecode
import SQLeanite.CorePageSource
import SQLeanite.CoreOverflow
import SQLeanite.CoreFileAdapter
import SQLeanite.CoreWidePageInverse

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

/-- The separator keys on an interior page, in cell order.

`CoreDecode.interiorChildren?` discards these, but a write needs them: routing to the
wrong leaf still produces a well-formed file. -/
def interiorSeparators? (page : List UInt8) : Option (List Nat) :=
  if page.length == PhysicalCodec.pageSize then
    match page with
    | 5 :: _ :: _ :: countHigh :: countLow :: _ :: _ :: _ ::
        _ :: _ :: _ :: _ :: afterHeader =>
        match CoreDecode.decodeOffsetList
            (FileFormat.decodeU16 countHigh countLow) afterHeader with
        | none => none
        | some offsets =>
            offsets.mapM fun offset =>
              match FileFormat.decodeVarint ((page.drop offset).drop 4) with
              | some (key, _) => some key.val
              | none => none
    | _ => none
  else none

/-- Interior cells as `(child page, largest key in that child)`, plus the rightmost
child.

Derived *from* `CoreDecode.interiorChildren?` rather than by parsing the page a second
time. An earlier version parsed independently, and then a fact about the descent could
not be transferred to a fact about the enumerated page set without matching two
separate `do`-notation parsers step for step. Taking the children from the same
decoder the rest of the module uses makes `interiorEntries_children` a short
structural proof instead. -/
def interiorEntries? (page : List UInt8) :
    Option (List (Nat × Nat) × Nat) :=
  match CoreDecode.interiorChildren? page with
  | none => none
  | some children =>
      match interiorSeparators? page with
      | none => none
      | some keys =>
          match children.reverse with
          | rightmost :: reversedInner =>
              if keys.length = reversedInner.length then
                some (reversedInner.reverse.zip keys, rightmost)
              else none
          | [] => none

/-- Both interior decoders agree on the children, by construction. -/
theorem interiorEntries_children {page : List UInt8}
    {entries : List (Nat × Nat)} {rightmost : Nat}
    (decoded : interiorEntries? page = some (entries, rightmost)) :
    CoreDecode.interiorChildren? page
      = some (entries.map Prod.fst ++ [rightmost]) := by
  unfold interiorEntries? at decoded
  split at decoded
  · exact absurd decoded (by simp)
  · rename_i children childrenResult
    split at decoded
    · exact absurd decoded (by simp)
    · rename_i keys _
      split at decoded
      · rename_i rightmost' reversedInner revShape
        split at decoded
        · rename_i lengths
          have pairEq := Option.some.inj decoded
          have fstEq : reversedInner.reverse.zip keys = entries :=
            congrArg Prod.fst pairEq
          have sndEq : rightmost' = rightmost := congrArg Prod.snd pairEq
          have shape : children = reversedInner.reverse ++ [rightmost'] := by
            have reversed := congrArg List.reverse revShape
            simpa using reversed
          rw [childrenResult, shape, sndEq, ← fstEq,
            List.map_fst_zip (by simp [lengths])]
        · exact absurd decoded (by simp)
      · exact absurd decoded (by simp)

/-- The leaf a key routes to, by descending interior separators. -/
def locateLeaf? (source : CoreDecode.PageSource) (key : Nat) :
    Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, pageNumber =>
      match source.readPage pageNumber with
      | none => none
      | some page =>
          match CoreDecode.interiorChildren? page with
          | none => some pageNumber
          | some _ =>
              -- A page with children but undecodable separators is not a leaf and
              -- cannot be routed through, so fail closed rather than write into it.
              match interiorEntries? page with
              | none => none
              | some (entries, rightmost) =>
                  let child :=
                    match entries.find? (fun entry => key ≤ entry.2) with
                    | some entry => entry.1
                    | none => rightmost
                  locateLeaf? source key fuel child

/-- Re-encode one leaf's rows.

Built on `CorePageCodec.encodeChunkLeaf` rather than on a private encoder so that
`CoreWidePageInverse.decodeRowsFrom_encodeChunkLeaf` -- the inverse the wide-page
work already proved -- applies directly. A single chunk holds the whole leaf. The
encoder returns `none` when the result would not fit a page, which sends the caller
to the whole-database path. -/
def encodeLeaf? (schema : Core.Schema) (rows : List Core.Row) :
    Option CoreFile.Page :=
  CorePageCodec.encodeChunkLeaf schema [(0, rows)]

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

**Proved, but not yet gated.** `insertPlan_refines` shows the plan this computes
denotes exactly the ordered insert, so the refinement is discharged. It is
*conditional* on `WellFormedTree` -- sound separators, disjoint sibling page sets,
inline leaves and in-range page numbers -- and this engine does not yet run those
checks at open time. Until decidable checkers for `TreeSound` and `TreeDisjoint`
exist and are proved sound, the premises are unverified at runtime, so the CLI
reaches this path only under an explicit opt-in. -/
def executeInsert? (syncOps : CoreFileAdapter.SyncOps)
    (paths : CoreFileAdapter.Paths) (tableName : String)
    (columns : Option (Array String)) (expressions : Array Expr) :
    IO (Option Core.Result) := do
  CoreFileAdapter.requireWritableFormat paths.main
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
  if schema.hasHiddenRowid || schema.autoIncrement then return none
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
`Option.bind_some` or `Option.bind`, and which `split` cannot see through. The way
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
      rcases Option.bind_eq_some_iff.mp mapped with ⟨headList, headResult, mapped⟩
      rcases Option.bind_eq_some_iff.mp mapped with ⟨tailLists, tailResult, mapped⟩
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
    (leafAgrees : ∀ p bytes, left.readPage p = some bytes →
      CoreDecode.decodeRowsFrom schema left bytes
        = CoreDecode.decodeRowsFrom schema right bytes)
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
      have leftPage : left.readPage pageNumber = some page := by
        rw [readEq]; exact pageResult
      cases interiorResult : CoreDecode.interiorChildren? page with
      | none => simpa [interiorResult] using leafAgrees pageNumber page leftPage
      | some children =>
          simp only [interiorResult]
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

/-- Inlineness transports between sources, because the only thing the decoder
consults the source for is an overflow chain, and there is none. -/
theorem PackedInline_congr (schema : Core.Schema)
    (left right : CoreDecode.PageSource) (fuelLeft fuelRight : Nat) :
    ∀ (count : Nat) (input : List UInt8),
      PackedInline schema left fuelLeft count input →
      PackedInline schema right fuelRight count input
  | 0, _, _ => trivial
  | count + 1, input, invariant =>
      ⟨invariant.1, by
        intro row afterRow decodedRight
        refine PackedInline_congr schema left right fuelLeft fuelRight count afterRow
          (invariant.2 row afterRow ?_)
        rw [decodeRowCellWithSuffixFrom_congr schema left right fuelLeft fuelRight
          input invariant.1]
        exact decodedRight⟩

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

theorem LeafInline_congr (schema : Core.Schema)
    (left right : CoreDecode.PageSource) (page : List UInt8)
    (inline : LeafInline schema left page) : LeafInline schema right page :=
  ⟨inline.1, fun count content content? =>
    PackedInline_congr schema left right _ _ count content
      (inline.2 count content content?)⟩

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

/-- `Option.bind_some` in the `>>=` form the `do`-notation elaborates to. Same
mismatch as `bind_congr'`: the library lemma is stated for `Option.bind` and does not
fire on `Bind.bind`. -/
@[simp] theorem some_bind' {α β : Type} (a : α) (f : α → Option β) :
    (some a >>= f) = f a := rfl

/-- The accumulator factors out of the interior fold.

`decodeSubtreeRowsFrom` accumulates children's rows with `foldlM`, so reasoning about
where a key lands means reasoning about that accumulator. Factoring it out turns the
fold into "decode the children, then prepend" and makes the `orderedUpsert`
distribution lemmas applicable. -/
theorem foldlM_acc {α β : Type} (f : α → Option (List β)) :
    ∀ (elements : List α) (acc : List β),
      elements.foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) acc
        = (elements.foldlM (fun a x => (f x).bind (fun r => some (a ++ r)))
            []).map (fun tail => acc ++ tail)
  | [], acc => by simp
  | x :: rest, acc => by
      simp only [List.foldlM_cons]
      cases headResult : f x with
      | none => simp
      | some head =>
          simp only [some_bind', Option.bind_some, List.nil_append]
          rw [foldlM_acc f rest (acc ++ head), foldlM_acc f rest head]
          cases restResult : rest.foldlM
              (fun a x => (f x).bind (fun r => some (a ++ r))) [] with
          | none => simp
          | some tail => simp [List.append_assoc]

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

/-- **Routing at a single leaf.** When the whole table lives in one leaf, a
page-local insert is exactly the ordered insert. This is the base case of the
routing argument and the shape the refinement composes over interior levels. -/
theorem singleLeaf_refines (schema : Core.Schema)
    (source : CoreDecode.PageSource) (fuel pageNumber : Nat)
    (page : List UInt8) (row : Core.Row) (rows : List Core.Row)
    (pageResult : source.readPage pageNumber = some page)
    (leaf : CoreDecode.interiorChildren? page = none)
    (decoded : CoreDecode.decodeRowsFrom schema source page = some rows) :
    CoreDecode.decodeSubtreeRowsFrom schema source (fuel + 1) pageNumber
      = some rows := by
  rw [CoreDecode.decodeSubtreeRowsFrom]
  rw [pageResult]
  simpa [leaf] using decoded

/-- **The refinement, single-leaf case.** Writing the re-encoded leaf produces bytes
denoting exactly the table with the row inserted.

This is the whole page-local argument for a table that fits one leaf: the write
replaces that leaf, the new bytes decode to the upserted rows, and no other page is
touched. Interior levels compose on top of it using `decodeSubtreeRowsFrom_congr`
for the untouched siblings and the `orderedUpsert` distribution lemmas to place the
key in the right one. -/
theorem singleLeaf_write_refines (schema : Core.Schema)
    (source : CoreDecode.PageSource)
    (pageWrite : GrowableStorage.PageWrite PhysicalCodec.pageSize)
    (fuel pageNumber : Nat) (page : List UInt8) (row : Core.Row)
    (rows : List Core.Row)
    (target : pageNumber = pageWrite.pageId + 1)
    (leafAfter : CoreDecode.interiorChildren?
      pageWrite.page.bytes.toList = none)
    (decodedAfter : CoreDecode.decodeRowsFrom schema
      (CorePageSource.write source pageWrite) pageWrite.page.bytes.toList
        = some (Core.orderedUpsert row rows)) :
    CoreDecode.decodeSubtreeRowsFrom schema
        (CorePageSource.write source pageWrite) (fuel + 1) pageNumber
      = some (Core.orderedUpsert row rows) := by
  refine singleLeaf_refines schema _ fuel pageNumber
    pageWrite.page.bytes.toList row _ ?_ leafAfter decodedAfter
  subst target
  simp only [CorePageSource.write]
  have notZero : ¬ (pageWrite.pageId + 1 = 0) := by omega
  have notBeyond : ¬ (max source.pageCount (pageWrite.pageId + 1)
      < pageWrite.pageId + 1) := by omega
  simp [notZero, notBeyond]

/-- Exactly one child owns the written page, when the children's page sets are
pairwise disjoint.

Disjointness is stated directly as a `Pairwise` rather than as `Nodup` on the
flattened list: without Mathlib there is no `nodup_append` to take apart, and the
`Pairwise` form is both what the interior walk naturally checks and what this
induction consumes. -/
theorem unique_child_owns {target : Nat} {nested : List (List Nat)}
    (disjoint : nested.Pairwise (fun left right => ∀ p ∈ left, p ∉ right))
    (owned : target ∈ nested.flatten) :
    ∃ before childList after,
      nested = before ++ childList :: after ∧
        target ∈ childList ∧
        (∀ other ∈ after, target ∉ other) := by
  induction nested with
  | nil => simp at owned
  | cons head rest induction =>
      rw [List.flatten_cons] at owned
      cases disjoint with
      | cons headDisjoint restDisjoint =>
          by_cases inHead : target ∈ head
          · exact ⟨[], head, rest, rfl, inHead,
              fun other member => headDisjoint other member target inHead⟩
          · have inRest : target ∈ rest.flatten := by
              rcases List.mem_append.mp owned with here | later
              · exact absurd here inHead
              · exact later
            rcases induction restDisjoint inRest with
              ⟨before, childList, after, shape, found, notAfter⟩
            exact ⟨head :: before, childList, after, by rw [shape]; rfl, found,
              notAfter⟩

/-- `locateLeaf?` always lands on a genuine leaf -- a page with no children.

This is the `targetIsLeaf` premise, and it is what makes the write safe to encode as
a leaf page. It holds because the descent stops only where `interiorChildren?` says
there is nothing to descend into; a page with children but unreadable separators
routes to `none` instead of being mistaken for a leaf. -/
theorem locateLeaf_entries_none (source : CoreDecode.PageSource) (key : Nat) :
    ∀ (fuel pageNumber leafPage : Nat),
      locateLeaf? source key fuel pageNumber = some leafPage →
      ∃ page, source.readPage leafPage = some page ∧
        CoreDecode.interiorChildren? page = none
  | 0, _, _, located => by simp [locateLeaf?] at located
  | fuel + 1, pageNumber, leafPage, located => by
      rw [locateLeaf?] at located
      split at located
      · exact absurd located (by simp)
      · rename_i page pageResult
        split at located
        · rename_i childrenResult
          exact ⟨page, by
            have equal : leafPage = pageNumber := (Option.some.inj located).symm
            rw [equal]; exact pageResult, childrenResult⟩
        · split at located
          · exact absurd located (by simp)
          · exact locateLeaf_entries_none source key fuel _ leafPage located

/-- The leaf `locateLeaf?` selects is one of the subtree's own pages.

Uses the bridge: the descent picks a child from `interiorEntries?`, and
`interiorEntries_children` says those are exactly the children `subtreePages`
enumerates, so the chosen child's page set is part of the parent's. Needs nothing
about whether the separators are *meaningful* -- only that the descent follows real
child pointers. This discharges the "the write is somewhere in this subtree" premise
that the routing induction carries. -/
theorem locateLeaf_mem_subtreePages (source : CoreDecode.PageSource) (key : Nat) :
    ∀ (fuel pageNumber : Nat) (pageList : List Nat) (leafPage : Nat),
      subtreePages source fuel pageNumber = some pageList →
      locateLeaf? source key fuel pageNumber = some leafPage →
      leafPage ∈ pageList
  | 0, _, _, _, _, located => by simp [locateLeaf?] at located
  | fuel + 1, pageNumber, pageList, leafPage, enumerated, located => by
      rw [locateLeaf?] at located
      split at located
      · exact absurd located (by simp)
      · rename_i page pageResult
        split at located
        · -- Stops here, so this page is the answer and roots the enumeration.
          have equal : leafPage = pageNumber := (Option.some.inj located).symm
          rw [equal]
          exact mem_subtreePages_self enumerated
        · split at located
          · exact absurd located (by simp)
          rename_i entries rightmost entriesResult
          have childrenResult := interiorEntries_children entriesResult
          simp only [subtreePages, pageResult, childrenResult] at enumerated
          cases nestedResult :
              (entries.map Prod.fst ++ [rightmost]).mapM (subtreePages source fuel) with
          | none => rw [nestedResult] at enumerated; simp at enumerated
          | some nested =>
              rw [nestedResult] at enumerated
              have listShape : pageList = pageNumber :: nested.flatten :=
                (Option.some.inj enumerated).symm
              have childMem : (match entries.find? (fun entry => key ≤ entry.2) with
                  | some entry => entry.1
                  | none => rightmost) ∈ entries.map Prod.fst ++ [rightmost] := by
                cases found : entries.find? (fun entry => key ≤ entry.2) with
                | none => simp [found]
                | some entry =>
                    have member := List.mem_of_find?_eq_some found
                    simp only [found]
                    exact List.mem_append_left _ (List.mem_map_of_mem member)
              rcases mapM_subtreePages_mem nestedResult _ childMem with
                ⟨childList, childEnumerated, subset⟩
              rw [listShape]
              exact List.mem_cons_of_mem pageNumber
                (subset leafPage (locateLeaf_mem_subtreePages source key fuel _
                  childList leafPage childEnumerated located))

/-- What routing has to establish: the subtree's rows split around the target leaf,
with the inserted key strictly between the two sides.

This is the premise the interior induction actually needs, and stating it explicitly
is the third correction to `subtree_write_refines`. The previous version assumed
`rows.Pairwise keyLess` plus "the write is somewhere in this subtree" was enough. It
is not: those say the table is sorted and the write is *somewhere*, not that the
inserted key belongs in *that* leaf. Writing an upserted leaf 1 when the key belongs
in leaf 5 satisfies every earlier premise and falsifies the conclusion.

Deriving this from `locateLeaf?` -- proving the descent lands where the separators
say it should -- is routing correctness proper, and is the remaining work. Splitting
it out here means the interior induction can be proved against a premise that is
true, rather than against one that quietly is not. -/
structure RoutedSplit (schema : Core.Schema) (source : CoreDecode.PageSource)
    (target : Nat) (row : Core.Row) (rows : List Core.Row) where
  before : List Core.Row
  leafRows : List Core.Row
  after : List Core.Row
  decomposition : rows = before ++ leafRows ++ after
  leafDecodes : ∀ oldLeaf, source.readPage target = some oldLeaf →
    CoreDecode.decodeRowsFrom schema source oldLeaf = some leafRows
  beforeBelow : ∀ earlier ∈ before, earlier.rowid.value < row.rowid.value
  afterAbove : ∀ later ∈ after, row.rowid.value < later.rowid.value

/-- The ordered insert on a routed split touches only the target leaf's segment.

This is the arithmetic content of routing, and it is proved: given the split, the
whole-table insert equals the leaf-local insert spliced back in place. What remains
unproved is only that `locateLeaf?` produces such a split. -/
theorem orderedUpsert_routedSplit (row : Core.Row)
    (before leafRows after : List Core.Row)
    (beforeBelow : ∀ earlier ∈ before, earlier.rowid.value < row.rowid.value)
    (afterAbove : ∀ later ∈ after, row.rowid.value < later.rowid.value) :
    Core.orderedUpsert row (before ++ leafRows ++ after)
      = before ++ Core.orderedUpsert row leafRows ++ after := by
  rw [orderedUpsert_append_of_beforeAll row (before ++ leafRows) after afterAbove,
    orderedUpsert_append_of_afterAll row before leafRows beforeBelow]

/-- Folding over a concatenation splits into the two halves' results.

Routing needs this because the chosen child sits between the children before it and
the children after it, and each group's rows have to be named separately to be
bounded separately. -/
theorem foldlM_split {α β : Type} (f : α → Option (List β))
    (left right : List α) (result : List β)
    (folded : (left ++ right).foldlM
        (fun a x => (f x).bind (fun r => some (a ++ r))) [] = some result) :
    ∃ leftRows rightRows,
      left.foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) [] = some leftRows ∧
      right.foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) [] = some rightRows ∧
      result = leftRows ++ rightRows := by
  rw [List.foldlM_append] at folded
  cases leftResult :
      left.foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) [] with
  | none => rw [leftResult] at folded; simp at folded
  | some leftRows =>
      rw [leftResult] at folded
      simp only [some_bind'] at folded
      rw [foldlM_acc f right leftRows] at folded
      cases rightResult :
          right.foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) [] with
      | none => rw [rightResult] at folded; simp at folded
      | some rightRows =>
          rw [rightResult] at folded
          exact ⟨leftRows, rightRows, rfl, rfl, by simpa using folded.symm⟩

/-- The converse of `foldlM_split`: two halves' results concatenate.

Needed in the write direction, where each group's rows are known separately and the
parent's fold has to be reassembled from them. -/
theorem foldlM_join {α β : Type} (f : α → Option (List β))
    (left right : List α) (leftRows rightRows : List β)
    (leftFold : left.foldlM
      (fun a x => (f x).bind (fun r => some (a ++ r))) [] = some leftRows)
    (rightFold : right.foldlM
      (fun a x => (f x).bind (fun r => some (a ++ r))) [] = some rightRows) :
    (left ++ right).foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) []
      = some (leftRows ++ rightRows) := by
  rw [List.foldlM_append, leftFold]
  simp only [some_bind']
  rw [foldlM_acc f right leftRows, rightFold]
  simp

/-- Every element of a fold's result came from some element of the input.

This is what turns a per-child bound into a bound on the concatenated rows: to show
every row before the target is below the key, it is enough to know which child each
row came from. -/
theorem foldlM_mem {α β : Type} (f : α → Option (List β)) :
    ∀ (elements : List α) (result : List β),
      elements.foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) []
          = some result →
      ∀ b ∈ result, ∃ x, x ∈ elements ∧ ∃ xs, f x = some xs ∧ b ∈ xs := by
  intro elements
  induction elements with
  | nil =>
      intro result folded b member
      simp at folded
      subst folded
      simp at member
  | cons x rest induction =>
      intro result folded b member
      rcases foldlM_split f [x] rest result (by simpa using folded) with
        ⟨headRows, tailRows, headFold, tailFold, shape⟩
      have headEq : f x = some headRows := by simpa using headFold
      subst shape
      rcases List.mem_append.mp member with inHead | inTail
      · exact ⟨x, List.mem_cons_self, headRows, headEq, inHead⟩
      · rcases induction tailRows tailFold b inTail with ⟨y, memY, ys, fy, inYs⟩
        exact ⟨y, List.mem_cons_of_mem x memY, ys, fy, inYs⟩

/-- A bound that holds of every child's rows holds of their concatenation. -/
theorem foldRows_bound (schema : Core.Schema) (source : CoreDecode.PageSource)
    (fuel : Nat) (P : Core.Row → Prop) (group : List Nat) (groupRows : List Core.Row)
    (childBound : ∀ child ∈ group, ∀ childRows,
      CoreDecode.decodeSubtreeRowsFrom schema source fuel child = some childRows →
      ∀ candidate ∈ childRows, P candidate)
    (folded : group.foldlM
      (fun a x => (CoreDecode.decodeSubtreeRowsFrom schema source fuel x).bind
        (fun r => some (a ++ r))) ([] : List Core.Row) = some groupRows) :
    ∀ candidate ∈ groupRows, P candidate := by
  intro candidate member
  rcases foldlM_mem _ group groupRows folded candidate member with
    ⟨child, childMem, childRows, childDecoded, rowMem⟩
  exact childBound child childMem childRows childDecoded candidate rowMem

/-- The subtree's separators really bound its children's rows.

This is the one premise that is about *meaning* rather than structure, and it is what
the 653 ms check in `docs/LAZY_WRITE_DESIGN.md` establishes: a tree-order walk of the
interior pages plus the first and last cell of every leaf, decoding no rows. Stated
recursively because routing descends recursively.

`bounded` is the separator contract: every row in a child's subtree is at or below
that child's separator key. `increasing` is what makes the children's row segments
line up in key order, so that `orderedUpsert_routedSplit` applies. -/
def TreeSound (schema : Core.Schema) (source : CoreDecode.PageSource) :
    Nat → Nat → Prop
  | 0, _ => False
  | fuel + 1, pageNumber =>
      ∀ page, source.readPage pageNumber = some page →
        ∀ entries rightmost, interiorEntries? page = some (entries, rightmost) →
          (∀ child ∈ rightmost :: entries.map Prod.fst,
              TreeSound schema source fuel child) ∧
            (∀ entry ∈ entries, ∀ childRows,
              CoreDecode.decodeSubtreeRowsFrom schema source fuel entry.1
                  = some childRows →
                ∀ candidate ∈ childRows, candidate.treeKey ≤ entry.2) ∧
            (∀ (pre : List (Nat × Nat)) (entry : Nat × Nat)
                (post : List (Nat × Nat)), entries = pre ++ entry :: post →
              ∀ later ∈ rightmost :: post.map Prod.fst, ∀ laterRows,
                CoreDecode.decodeSubtreeRowsFrom schema source fuel later
                    = some laterRows →
                ∀ candidate ∈ laterRows, entry.2 < candidate.treeKey)

/-- The routing key is the rowid biased by a fixed midpoint, so it orders rows the
same way. Separators are compared in key space; `orderedUpsert` in rowid space. -/
theorem value_lt_of_treeKey_lt {left right : Core.Row}
    (less : left.treeKey < right.treeKey) :
    left.rowid.value < right.rowid.value :=
  (Core.Row.treeKey_lt_iff left right).mp less

/-- Sibling subtrees own disjoint page sets.

Stated recursively, in the shape routing consumes: the child the descent enters owns
its pages, so a write inside it is invisible to its siblings. Without this the frame
step is simply false -- a page reachable from two subtrees would change both.

This is what the 80 ms interior-only walk checks. Page identities live in interior
pages, so enumerating every page id and finding no duplicate needs no row decode. -/
def TreeDisjoint (source : CoreDecode.PageSource) : Nat → Nat → Prop
  | 0, _ => False
  | fuel + 1, pageNumber =>
      ∀ page, source.readPage pageNumber = some page →
        ∀ children, CoreDecode.interiorChildren? page = some children →
          (∀ child ∈ children, TreeDisjoint source fuel child) ∧
            ∀ (pre : List Nat) (chosen : Nat) (post : List Nat),
              children = pre ++ chosen :: post →
              ∀ other ∈ pre ++ post, ∀ otherList chosenList,
                subtreePages source fuel other = some otherList →
                subtreePages source fuel chosen = some chosenList →
                ∀ p ∈ chosenList, p ∉ otherList

/-- **The remaining obligation.** A sound tree routes a key to the leaf whose segment
it belongs in, which is exactly a `RoutedSplit`.

With this, `orderedUpsert_routedSplit` gives the whole-table insert, the frame chain
gives the untouched pages, and `insertPlan_refines` follows. Everything else in this
module is proved; this is the single step where the checked ordering premise has to do
work rather than the structural facts.

The proof is an induction on the descent: at each interior page the separators split
the children into those wholly below the key and those wholly above, `TreeSound.bounded`
and `.increasing` place the chosen child between them, and the recursive call supplies
the split one level down. -/
theorem locateLeaf_routedSplit (schema : Core.Schema)
    (source : CoreDecode.PageSource) (key : Nat) (row : Core.Row)
    (keyIsRow : row.treeKey = key) :
    ∀ (fuel pageNumber leafPage : Nat) (rows : List Core.Row),
      TreeSound schema source fuel pageNumber →
      CoreDecode.decodeSubtreeRowsFrom schema source fuel pageNumber = some rows →
      locateLeaf? source key fuel pageNumber = some leafPage →
      Nonempty (RoutedSplit schema source leafPage row rows) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ sound _ _; simp [TreeSound] at sound
  | succ fuel induction =>
    intro pageNumber leafPage rows sound decoded located
    rw [locateLeaf?] at located
    split at located
    · exact absurd located (by simp)
    rename_i page pageResult
    simp only [CoreDecode.decodeSubtreeRowsFrom, pageResult, some_bind'] at decoded
    split at located
    · -- A genuine leaf: the subtree is this one page, so the split is trivial.
      rename_i childrenResult
      simp only [childrenResult] at decoded
      have equal : leafPage = pageNumber := (Option.some.inj located).symm
      exact ⟨{ before := [], leafRows := rows, after := []
               decomposition := by simp
               leafDecodes := by
                 intro oldLeaf readLeaf
                 rw [equal, pageResult] at readLeaf
                 rw [← Option.some.inj readLeaf]
                 exact decoded
               beforeBelow := by simp
               afterAbove := by simp }⟩
    rename_i children childrenResult
    split at located
    · exact absurd located (by simp)
    rename_i entries rightmost entriesResult
    have childrenShape : children = entries.map Prod.fst ++ [rightmost] := by
      have viaEntries := interiorEntries_children entriesResult
      rw [childrenResult] at viaEntries
      exact Option.some.inj viaEntries
    subst childrenShape
    simp only [childrenResult] at decoded
    obtain ⟨soundChildren, bounded, above⟩ :=
      sound page pageResult entries rightmost entriesResult
    have decodedFold :
        (entries.map Prod.fst ++ [rightmost]).foldlM
          (fun a x => (CoreDecode.decodeSubtreeRowsFrom schema source fuel x).bind
            (fun r => some (a ++ r))) ([] : List Core.Row) = some rows := decoded
    cases found : entries.find? (fun entry => key ≤ entry.2) with
    | none =>
        -- No separator covers the key, so it belongs in the rightmost child and
        -- every other child is wholly below it.
        simp only [found] at located
        rcases foldlM_split _ (entries.map Prod.fst) [rightmost] rows decodedFold with
          ⟨preRows, restRows, preFold, restFold, shape⟩
        have restDecoded :
            CoreDecode.decodeSubtreeRowsFrom schema source fuel rightmost
              = some restRows := by simpa using restFold
        rcases induction rightmost leafPage restRows
            (soundChildren rightmost (by simp)) restDecoded located with
          ⟨⟨tailBefore, tailLeaf, tailAfter, tailShape, tailDecodes, tailBelow,
            tailAbove⟩⟩
        refine ⟨{ before := preRows ++ tailBefore
                  leafRows := tailLeaf
                  after := tailAfter
                  decomposition := by rw [shape, tailShape]; simp
                  leafDecodes := tailDecodes
                  afterAbove := tailAbove
                  beforeBelow := ?_ }⟩
        intro earlier member
        rcases List.mem_append.mp member with inPre | inSplit
        · rcases foldlM_mem _ (entries.map Prod.fst) preRows preFold earlier inPre with
            ⟨child, childMem, childRows, childDecoded, rowMem⟩
          rcases List.mem_map.mp childMem with ⟨entry, entryMem, entryEq⟩
          have le := bounded entry entryMem childRows
            (by rw [← entryEq] at childDecoded; exact childDecoded) earlier rowMem
          have lt : entry.2 < key := by
            have missed := (List.find?_eq_none).mp found entry entryMem
            simp at missed
            omega
          refine value_lt_of_treeKey_lt ?_
          rw [keyIsRow]
          omega
        · exact tailBelow earlier inSplit
    | some entry =>
        -- `entry` is the first separator at or above the key: children before it are
        -- wholly below the key, children after it are wholly above `entry.2 ≥ key`.
        simp only [found] at located
        rcases List.find?_eq_some_iff_append.mp found with
          ⟨keyLe, pre, post, entriesShape, preFails⟩
        simp at keyLe
        subst entriesShape
        rw [show ((pre ++ entry :: post).map Prod.fst ++ [rightmost])
              = pre.map Prod.fst ++ ([entry.1] ++ (post.map Prod.fst ++ [rightmost]))
            from by simp] at decodedFold
        rcases foldlM_split _ (pre.map Prod.fst) _ rows decodedFold with
          ⟨preRows, tailRows, preFold, tailFold, shape₁⟩
        rcases foldlM_split _ [entry.1] (post.map Prod.fst ++ [rightmost]) tailRows
          tailFold with ⟨chosenRows, postRows, chosenFold, postFold, shape₂⟩
        have chosenDecoded :
            CoreDecode.decodeSubtreeRowsFrom schema source fuel entry.1
              = some chosenRows := by simpa using chosenFold
        rcases induction entry.1 leafPage chosenRows
            (soundChildren entry.1 (by simp)) chosenDecoded located with
          ⟨⟨midBefore, midLeaf, midAfter, midShape, midDecodes, midBelow, midAbove⟩⟩
        refine ⟨{ before := preRows ++ midBefore
                  leafRows := midLeaf
                  after := midAfter ++ postRows
                  decomposition := by rw [shape₁, shape₂, midShape]; simp
                  leafDecodes := midDecodes
                  beforeBelow := ?_
                  afterAbove := ?_ }⟩
        · intro earlier member
          rcases List.mem_append.mp member with inPre | inSplit
          · rcases foldlM_mem _ (pre.map Prod.fst) preRows preFold earlier inPre with
              ⟨child, childMem, childRows, childDecoded, rowMem⟩
            rcases List.mem_map.mp childMem with ⟨earlierEntry, entryMem, entryEq⟩
            have le := bounded earlierEntry (List.mem_append_left _ entryMem) childRows
              (by rw [← entryEq] at childDecoded; exact childDecoded)
              earlier rowMem
            have lt : earlierEntry.2 < key := by
              have missed := preFails earlierEntry entryMem
              simp at missed
              omega
            refine value_lt_of_treeKey_lt ?_
            rw [keyIsRow]
            omega
          · exact midBelow earlier inSplit
        · intro later member
          rcases List.mem_append.mp member with inSplit | inPost
          · exact midAbove later inSplit
          · rcases foldlM_mem _ (post.map Prod.fst ++ [rightmost]) postRows postFold
              later inPost with ⟨child, childMem, childRows, childDecoded, rowMem⟩
            have memAlt : child ∈ rightmost :: post.map Prod.fst := by
              rcases List.mem_append.mp childMem with inPost' | isRightmost
              · exact List.mem_cons_of_mem _ inPost'
              · simp at isRightmost
                simp [isRightmost]
            have gt := above pre entry post rfl child memAlt childRows childDecoded
              later rowMem
            refine value_lt_of_treeKey_lt ?_
            rw [keyIsRow]
            omega

/-- What a page-local write needs to know about the on-disk tree.

Every field is a *checked* premise, not an assumption, and none of them decodes a
row. `separators` and `disjoint` are established by walking interior pages and each
leaf's first and last cell -- 653 ms on the 1,000,000-row file, against 143,671 ms
for the whole-database open they replace. `inline` is the counting check: if the
enumerated tree pages, page one and the freelist account for every page in the file,
no overflow page exists. So the generated-image stamp keeps its existing weaker
role. -/
structure WellFormedTree (schema : Core.Schema) (source : CoreDecode.PageSource)
    (fuel rootPage : Nat) where
  pages : List Nat
  enumerated : subtreePages source fuel rootPage = some pages
  separators : TreeSound schema source fuel rootPage
  disjoint : TreeDisjoint source fuel rootPage
  inline : ∀ p bytes, source.readPage p = some bytes → LeafInline schema source bytes
  bounded : ∀ p, (p = 0 ∨ source.pageCount < p) → source.readPage p = none
  rows : List Core.Row
  decoded : CoreDecode.decodeSubtreeRowsFrom schema source fuel rootPage = some rows

/-- **The write, routed through the tree.** Rewriting the located leaf changes the
subtree's rows by exactly the ordered insert, and changes nothing else.

Frame and routing have to be one induction rather than two lemmas: the frame step
needs to know *which* child owns the written page, and that is what the descent
decides. Siblings are carried by `decodeSubtreeRowsFrom_congr`, the chosen child by
the induction hypothesis, and `orderedUpsert_routedSplit` splices the three groups
back together. -/
theorem locateLeaf_write_refines (schema : Core.Schema)
    (source new : CoreDecode.PageSource) (key : Nat) (row : Core.Row)
    (keyIsRow : row.treeKey = key)
    (leafPage : Nat) (oldLeafRows : List Core.Row)
    (leafAgrees : ∀ p bytes, source.readPage p = some bytes →
      CoreDecode.decodeRowsFrom schema source bytes
        = CoreDecode.decodeRowsFrom schema new bytes)
    (offTarget : ∀ p, p ≠ leafPage → source.readPage p = new.readPage p)
    (oldTarget : ∀ oldLeaf, source.readPage leafPage = some oldLeaf →
      CoreDecode.decodeRowsFrom schema source oldLeaf = some oldLeafRows)
    (newLeaf : List UInt8)
    (newRead : new.readPage leafPage = some newLeaf)
    (newIsLeaf : CoreDecode.interiorChildren? newLeaf = none)
    (newDecoded : CoreDecode.decodeRowsFrom schema new newLeaf
      = some (Core.orderedUpsert row oldLeafRows)) :
    ∀ (fuel pageNumber : Nat) (rows : List Core.Row) (pageList : List Nat),
      TreeSound schema source fuel pageNumber →
      TreeDisjoint source fuel pageNumber →
      subtreePages source fuel pageNumber = some pageList →
      CoreDecode.decodeSubtreeRowsFrom schema source fuel pageNumber = some rows →
      locateLeaf? source key fuel pageNumber = some leafPage →
      CoreDecode.decodeSubtreeRowsFrom schema new fuel pageNumber
        = some (Core.orderedUpsert row rows) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ sound _ _ _ _; simp [TreeSound] at sound
  | succ fuel induction =>
    intro pageNumber rows pageList sound disjoint enumerated decoded located
    have located₀ := located
    rw [locateLeaf?] at located
    split at located
    · exact absurd located (by simp)
    rename_i page pageResult
    simp only [CoreDecode.decodeSubtreeRowsFrom, pageResult, some_bind'] at decoded
    split at located
    · -- The descent stops here, so the subtree is this one leaf and the write is
      -- the whole of it.
      rename_i childrenResult
      simp only [childrenResult] at decoded
      have equal : leafPage = pageNumber := (Option.some.inj located).symm
      have oldEq : oldLeafRows = rows :=
        Option.some.inj
          ((oldTarget page (by rw [equal]; exact pageResult)).symm.trans decoded)
      refine singleLeaf_refines schema new fuel pageNumber newLeaf row _
        (by rw [← equal]; exact newRead) newIsLeaf ?_
      rw [newDecoded, oldEq]
    rename_i children childrenResult
    split at located
    · exact absurd located (by simp)
    rename_i entries rightmost entriesResult
    have childrenShape : children = entries.map Prod.fst ++ [rightmost] := by
      have viaEntries := interiorEntries_children entriesResult
      rw [childrenResult] at viaEntries
      exact Option.some.inj viaEntries
    subst childrenShape
    simp only [childrenResult] at decoded
    obtain ⟨soundChildren, bounded, above⟩ :=
      sound page pageResult entries rightmost entriesResult
    obtain ⟨disjointChildren, siblingsDisjoint⟩ :=
      disjoint page pageResult _ childrenResult
    -- This page has children, so it is not the leaf that was written.
    have pageNe : pageNumber ≠ leafPage := by
      intro same
      rcases locateLeaf_entries_none source key (fuel + 1) pageNumber leafPage located₀
        with ⟨leafBytes, leafRead, leafNoChildren⟩
      rw [← same, pageResult] at leafRead
      rw [← Option.some.inj leafRead, childrenResult] at leafNoChildren
      exact absurd leafNoChildren (by simp)
    have newPage : new.readPage pageNumber = some page := by
      rw [← offTarget pageNumber pageNe]; exact pageResult
    -- Split the children into those wholly below the key, the one it routes to, and
    -- those wholly above it.  Both `find?` outcomes give the same shape.
    obtain ⟨preChildren, chosen, postChildren, split, preBelow, postAbove, chosenEq⟩ :
        ∃ preChildren chosen postChildren,
          entries.map Prod.fst ++ [rightmost]
              = preChildren ++ chosen :: postChildren ∧
          (∀ child ∈ preChildren, ∀ childRows,
            CoreDecode.decodeSubtreeRowsFrom schema source fuel child
                = some childRows →
            ∀ candidate ∈ childRows,
              candidate.rowid.value < row.rowid.value) ∧
          (∀ child ∈ postChildren, ∀ childRows,
            CoreDecode.decodeSubtreeRowsFrom schema source fuel child
                = some childRows →
            ∀ candidate ∈ childRows,
              row.rowid.value < candidate.rowid.value) ∧
          chosen = (match entries.find? (fun entry => key ≤ entry.2) with
            | some entry => entry.1
            | none => rightmost) := by
      cases found : entries.find? (fun entry => key ≤ entry.2) with
      | none =>
          refine ⟨entries.map Prod.fst, rightmost, [], by simp, ?_, by simp,
            by simp [found]⟩
          intro child childMem childRows childDecoded candidate rowMem
          rcases List.mem_map.mp childMem with ⟨entry, entryMem, entryEq⟩
          rw [← entryEq] at childDecoded
          have le := bounded entry entryMem childRows childDecoded candidate rowMem
          have missed := (List.find?_eq_none).mp found entry entryMem
          simp at missed
          refine value_lt_of_treeKey_lt ?_
          rw [keyIsRow]
          omega
      | some entry =>
          rcases List.find?_eq_some_iff_append.mp found with
            ⟨keyLe, pre, post, entriesShape, preFails⟩
          simp at keyLe
          subst entriesShape
          refine ⟨pre.map Prod.fst, entry.1, post.map Prod.fst ++ [rightmost],
            by simp, ?_, ?_, by simp [found]⟩
          · intro child childMem childRows childDecoded candidate rowMem
            rcases List.mem_map.mp childMem with ⟨earlier, earlierMem, earlierEq⟩
            rw [← earlierEq] at childDecoded
            have le := bounded earlier (List.mem_append_left _ earlierMem) childRows
              childDecoded candidate rowMem
            have missed := preFails earlier earlierMem
            simp at missed
            refine value_lt_of_treeKey_lt ?_
            rw [keyIsRow]
            omega
          · intro child childMem childRows childDecoded candidate rowMem
            have memAlt : child ∈ rightmost :: post.map Prod.fst := by
              rcases List.mem_append.mp childMem with inPost | isRightmost
              · exact List.mem_cons_of_mem _ inPost
              · simp at isRightmost
                simp [isRightmost]
            have gt := above pre entry post rfl child memAlt childRows childDecoded
              candidate rowMem
            refine value_lt_of_treeKey_lt ?_
            rw [keyIsRow]
            omega
    have chosenMemChildren : chosen ∈ entries.map Prod.fst ++ [rightmost] := by
      rw [split]; simp
    have chosenSound : TreeSound schema source fuel chosen := by
      refine soundChildren chosen ?_
      rcases List.mem_append.mp chosenMemChildren with inEntries | isRightmost
      · exact List.mem_cons_of_mem _ inEntries
      · simp at isRightmost
        simp [isRightmost]
    rw [split] at childrenResult decoded
    cases nestedResult :
        (preChildren ++ chosen :: postChildren).mapM (subtreePages source fuel) with
    | none =>
        simp only [subtreePages, pageResult, childrenResult, nestedResult] at enumerated
        exact absurd enumerated (by simp)
    | some nested =>
    rcases foldlM_split _ preChildren (chosen :: postChildren) rows decoded with
      ⟨preRows, tailRows, preFold, tailFold, shape₁⟩
    rcases foldlM_split _ [chosen] postChildren tailRows (by simpa using tailFold) with
      ⟨chosenRows, postRows, chosenFold, postFold, shape₂⟩
    have chosenDecoded :
        CoreDecode.decodeSubtreeRowsFrom schema source fuel chosen
          = some chosenRows := by simpa using chosenFold
    have locatedChosen : locateLeaf? source key fuel chosen = some leafPage := by
      rw [chosenEq]; exact located
    rcases mapM_subtreePages_mem nestedResult chosen (by simp) with
      ⟨chosenList, chosenEnum, _⟩
    have targetMem : leafPage ∈ chosenList :=
      locateLeaf_mem_subtreePages source key fuel chosen chosenList leafPage
        chosenEnum locatedChosen
    -- Siblings cannot see the written page, so their rows are unchanged.
    have siblingSame : ∀ child ∈ preChildren ++ postChildren,
        CoreDecode.decodeSubtreeRowsFrom schema source fuel child
          = CoreDecode.decodeSubtreeRowsFrom schema new fuel child := by
      intro child childMem
      have childMem' : child ∈ preChildren ++ chosen :: postChildren := by
        rcases List.mem_append.mp childMem with inPre | inPost
        · exact List.mem_append_left _ inPre
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ inPost)
      rcases mapM_subtreePages_mem nestedResult child childMem' with
        ⟨childList, childEnum, _⟩
      refine decodeSubtreeRowsFrom_congr schema source new leafAgrees childEnum ?_
      intro p pMem
      refine offTarget p ?_
      intro same
      exact (siblingsDisjoint preChildren chosen postChildren split child childMem
        childList chosenList childEnum chosenEnum leafPage targetMem) (same ▸ pMem)
    have preNew : preChildren.foldlM
        (fun a x => (CoreDecode.decodeSubtreeRowsFrom schema new fuel x).bind
          (fun r => some (a ++ r))) ([] : List Core.Row) = some preRows := by
      rw [← preFold]
      exact foldlM_congr fun _ child member => by
        rw [siblingSame child (List.mem_append_left _ member)]
    have postNew : postChildren.foldlM
        (fun a x => (CoreDecode.decodeSubtreeRowsFrom schema new fuel x).bind
          (fun r => some (a ++ r))) ([] : List Core.Row) = some postRows := by
      rw [← postFold]
      exact foldlM_congr fun _ child member => by
        rw [siblingSame child (List.mem_append_right _ member)]
    have chosenNew : CoreDecode.decodeSubtreeRowsFrom schema new fuel chosen
        = some (Core.orderedUpsert row chosenRows) :=
      induction chosen chosenRows chosenList chosenSound
        (disjointChildren chosen chosenMemChildren) chosenEnum chosenDecoded
        locatedChosen
    have wholeNew : (preChildren ++ ([chosen] ++ postChildren)).foldlM
        (fun a x => (CoreDecode.decodeSubtreeRowsFrom schema new fuel x).bind
          (fun r => some (a ++ r))) ([] : List Core.Row)
        = some (preRows ++ (Core.orderedUpsert row chosenRows ++ postRows)) :=
      foldlM_join _ preChildren _ _ _ preNew
        (foldlM_join _ [chosen] postChildren _ _ (by simpa using chosenNew) postNew)
    have preRowsBelow : ∀ earlier ∈ preRows, earlier.rowid.value < row.rowid.value :=
      foldRows_bound schema source fuel _ preChildren preRows preBelow preFold
    have postRowsAbove : ∀ later ∈ postRows, row.rowid.value < later.rowid.value :=
      foldRows_bound schema source fuel _ postChildren postRows postAbove postFold
    have rowsShape : rows = preRows ++ chosenRows ++ postRows := by
      rw [shape₁, shape₂]; simp
    rw [CoreDecode.decodeSubtreeRowsFrom, newPage]
    simp only [some_bind', childrenResult]
    rw [rowsShape,
      orderedUpsert_routedSplit row preRows chosenRows postRows preRowsBelow
        postRowsAbove]
    simpa using wholeNew

/-- The ordered insert introduces no row other than the one being inserted. -/
theorem mem_orderedUpsert (row : Core.Row) :
    ∀ (rows : List Core.Row) (candidate : Core.Row),
      candidate ∈ Core.orderedUpsert row rows → candidate = row ∨ candidate ∈ rows
  | [], candidate, member => by
      simp only [Core.orderedUpsert, List.mem_singleton] at member
      exact Or.inl member
  | existing :: rows, candidate, member => by
      rw [Core.orderedUpsert] at member
      split at member
      · rcases List.mem_cons.mp member with isRow | rest
        · exact Or.inl isRow
        · exact Or.inr rest
      · split at member
        · rcases List.mem_cons.mp member with isExisting | rest
          · exact Or.inr (isExisting ▸ List.mem_cons_self)
          · rcases mem_orderedUpsert row rows candidate rest with isRow | inRows
            · exact Or.inl isRow
            · exact Or.inr (List.mem_cons_of_mem _ inRows)
        · rcases List.mem_cons.mp member with isRow | rest
          · exact Or.inl isRow
          · exact Or.inr (List.mem_cons_of_mem _ rest)

/-- **The top-level refinement.** The plan the executable computes, applied to the
file, denotes exactly the table with the row inserted -- which is what
`Core.execute` produces for that `INSERT`.

This is the statement `executeInsert?` must be gated on before the page-local path
may be reachable from a shipped build. -/
theorem insertPlan_refines (schema : Core.Schema)
    (source : CoreDecode.PageSource) (rootPage : Nat) (row : Core.Row)
    (leafPage : Nat) (encoded : CoreFile.Page) (rows : List Core.Row)
    (wellFormed : WellFormedTree schema source (source.pageCount + 1) rootPage)
    (decoded : CoreDecode.decodeSubtreeRowsFrom schema source
      (source.pageCount + 1) rootPage = some rows)
    (rowsEncodable : ∀ candidate ∈ rows,
      candidate.WellFormed schema ∧ CoreOverflow.RowInline schema candidate)
    (rowEncodable : row.WellFormed schema ∧ CoreOverflow.RowInline schema row)
    (planned : insertPlan? schema source rootPage row = some (leafPage, encoded)) :
    CoreDecode.decodeSubtreeRowsFrom schema
        (CorePageSource.write source ⟨leafPage - 1, encoded.storage⟩)
        (source.pageCount + 1) rootPage
      = some (Core.orderedUpsert row rows) := by
  rw [insertPlan?] at planned
  split at planned
  · exact absurd planned (by simp)
  rename_i planLeaf locatedPlan
  split at planned
  · exact absurd planned (by simp)
  rename_i oldLeaf oldRead
  split at planned
  · exact absurd planned (by simp)
  rename_i leafRows leafDecoded
  split at planned
  · exact absurd planned (by simp)
  split at planned
  · exact absurd planned (by simp)
  rename_i encodedPage encodedResult
  obtain ⟨targetEq, encodedEq⟩ : planLeaf = leafPage ∧ encodedPage = encoded := by
    have injected := Option.some.inj planned
    exact ⟨congrArg Prod.fst injected, congrArg Prod.snd injected⟩
  subst targetEq
  subst encodedEq
  -- The written page is a real page of the file, which fixes the renumbering.
  have leafPos : 0 < planLeaf := by
    rcases Nat.eq_zero_or_pos planLeaf with zero | positive
    · rw [zero, wellFormed.bounded 0 (Or.inl rfl)] at oldRead
      exact absurd oldRead (by simp)
    · exact positive
  have leafLe : planLeaf ≤ source.pageCount := by
    rcases Nat.lt_or_ge source.pageCount planLeaf with beyond | within
    · rw [wellFormed.bounded planLeaf (Or.inr beyond)] at oldRead
      exact absurd oldRead (by simp)
    · exact within
  have countEq : max source.pageCount (planLeaf - 1 + 1) = source.pageCount := by omega
  -- Inline leaves decode the same from either source, which is the frame premise.
  have leafAgrees : ∀ p bytes, source.readPage p = some bytes →
      CoreDecode.decodeRowsFrom schema source bytes
        = CoreDecode.decodeRowsFrom schema
            (CorePageSource.write source ⟨planLeaf - 1, encodedPage.storage⟩) bytes := by
    intro p bytes read
    exact decodeRowsFrom_congr schema source _ bytes (wellFormed.inline p bytes read)
      (LeafInline_congr schema source _ bytes (wellFormed.inline p bytes read))
  have offTarget : ∀ p, p ≠ planLeaf → source.readPage p
      = (CorePageSource.write source ⟨planLeaf - 1, encodedPage.storage⟩).readPage p := by
    intro p notTarget
    simp only [CorePageSource.write, countEq]
    by_cases zero : p = 0
    · simp [zero, wellFormed.bounded 0 (Or.inl rfl)]
    by_cases beyond : source.pageCount < p
    · simp [zero, beyond, wellFormed.bounded p (Or.inr beyond)]
    · have notWritten : ¬ (p = planLeaf - 1 + 1) := by omega
      simp [zero, beyond, notWritten]
  have newRead :
      (CorePageSource.write source ⟨planLeaf - 1, encodedPage.storage⟩).readPage planLeaf
        = some encodedPage.bytes := by
    simp only [CorePageSource.write, countEq]
    have notZero : ¬ (planLeaf = 0) := by omega
    have notBeyond : ¬ (source.pageCount < planLeaf) := by omega
    have isWritten : planLeaf = planLeaf - 1 + 1 := by omega
    simp [notZero, notBeyond, ← isWritten, CoreFile.Page.storage]
  -- The leaf's rows are a segment of the table's, so they inherit encodability.
  rcases locateLeaf_routedSplit schema source row.treeKey row rfl
      (source.pageCount + 1) rootPage planLeaf rows wellFormed.separators decoded
      locatedPlan with ⟨routed⟩
  have leafSubset : ∀ candidate ∈ leafRows, candidate ∈ rows := by
    intro candidate member
    have leafEq : routed.leafRows = leafRows :=
      Option.some.inj ((routed.leafDecodes oldLeaf oldRead).symm.trans leafDecoded)
    rw [routed.decomposition, leafEq]
    exact List.mem_append_left _ (List.mem_append_right _ member)
  have newRowsEncodable : ∀ candidate ∈ Core.orderedUpsert row leafRows,
      candidate.WellFormed schema ∧ CoreOverflow.RowInline schema candidate := by
    intro candidate member
    rcases mem_orderedUpsert row leafRows candidate member with isRow | inLeaf
    · rw [isRow]; exact rowEncodable
    · exact rowsEncodable candidate (leafSubset candidate inLeaf)
  have chunkEncoded : CorePageCodec.encodeChunkLeaf schema
      [(0, Core.orderedUpsert row leafRows)] = some encodedPage := encodedResult
  have newIsLeaf : CoreDecode.interiorChildren? encodedPage.bytes = none :=
    CorePageCodec.interiorChildren_encodeChunkLeaf schema _ encodedPage chunkEncoded
  have newDecoded : CoreDecode.decodeRowsFrom schema
      (CorePageSource.write source ⟨planLeaf - 1, encodedPage.storage⟩) encodedPage.bytes
        = some (Core.orderedUpsert row leafRows) := by
    have inverse := CoreWidePageInverse.decodeRowsFrom_encodeChunkLeaf schema
      [(0, Core.orderedUpsert row leafRows)] encodedPage
      (by
        intro entry entryMem candidate candidateMem
        simp only [List.mem_singleton] at entryMem
        subst entryMem
        exact (newRowsEncodable candidate candidateMem).1)
      (by
        intro entry entryMem candidate candidateMem
        simp only [List.mem_singleton] at entryMem
        subst entryMem
        exact (newRowsEncodable candidate candidateMem).2)
      chunkEncoded
      (CorePageSource.write source ⟨planLeaf - 1, encodedPage.storage⟩)
    simpa using inverse
  exact locateLeaf_write_refines schema source _ row.treeKey row rfl planLeaf leafRows
    leafAgrees offTarget
    (fun candidate read => by
      rw [oldRead] at read
      rw [← Option.some.inj read]
      exact leafDecoded)
    encodedPage.bytes newRead newIsLeaf newDecoded
    (source.pageCount + 1) rootPage rows wellFormed.pages wellFormed.separators
    wellFormed.disjoint wellFormed.enumerated decoded locatedPlan

end CoreLazyWrite
end SQLeanite
