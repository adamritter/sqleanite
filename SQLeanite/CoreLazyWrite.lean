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

/-! ## Refinement obligations

The executable above meets item 3's acceptance criterion and agrees with C SQLite on
every case exercised, but it is **not proved** to agree with `Core.execute`. Until
these are discharged it must not be reachable from a shipped build.

The decomposition is in `docs/LAZY_WRITE_DESIGN.md`: frame (other pages unchanged),
concatenation (a table's rows are its leaves' rows in page order), and routing (a
key belongs to exactly one leaf).

**Where the proof is stuck.** Both `CoreDecode.decodeSubtreeRowsFrom` and
`CoreDecode.decodeRowsFrom` are written with `do`-notation. Its `Option` bind is not
reduced by `dsimp`, `Option.bind_some`, `Option.some_bind` or `Option.bind`, and
`split` cannot see through it, so case analysis on the recursion is impractical as
written. The way forward is an explicit-match restatement of
`decodeSubtreeRowsFrom` proved by `rfl` -- attempted, and the restatement needs its
`foldlM` types pinned down -- after which the induction follows the shape below.
Restating the definitions themselves with explicit matches, as `subtreePages` does,
would remove the obstacle for good. -/

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
    (leafAgrees : ∀ page, CoreDecode.decodeRowsFrom schema left page
      = CoreDecode.decodeRowsFrom schema right page)
    {fuel pageNumber : Nat} {pageList : List Nat}
    (enumerated : subtreePages left fuel pageNumber = some pageList)
    (agree : ∀ p ∈ pageList, left.readPage p = right.readPage p) :
    CoreDecode.decodeSubtreeRowsFrom schema left fuel pageNumber
      = CoreDecode.decodeSubtreeRowsFrom schema right fuel pageNumber := by
  sorry

end CoreLazyWrite
end SQLeanite
