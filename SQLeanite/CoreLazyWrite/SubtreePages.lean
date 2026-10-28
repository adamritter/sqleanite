import SQLeanite.CoreFileAdapter.LookupGeneratedIndexCandidates
import SQLeanite.CoreWidePageInverse.DecodeOffsetListEncoded

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
  CoreFileAdapter.requireWritableAccess paths.main
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

end CoreLazyWrite

end SQLeanite
