import SQLeanite.CoreLazyWrite.SubtreePages
import SQLeanite.CoreLazyWrite.DecodeRowsByPointersFromCongr
import SQLeanite.CoreLazyWrite.TreeDisjoint
import SQLeanite.CoreLazyWrite.InsertPlanRefines

/-! Compatibility import for the responsibility modules above. -/

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

/-! ## Routing

Frame says a page write leaves other subtrees alone. Routing says the write lands in
the *right* subtree: the key belongs to exactly one leaf, so the whole table changes
by exactly one ordered insert. The two lemmas below are the arithmetic core --
`orderedUpsert` only disturbs the segment a key belongs to.
-/
