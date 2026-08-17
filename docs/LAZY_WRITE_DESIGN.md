# Design: a page-local write path

Status: design agreed, implementation in progress. This closes open-work item 3 in
the paper programme.

## The problem, measured

On the 583 MB, 1,000,000-row database:

| operation | cost |
|---|---:|
| one `SELECT` by primary key | **12 ms** |
| one autocommit `INSERT` | **143,671 ms** |

Reads are page-directed: `CoreLazyFileEngine` reads the catalog, walks a root-to-leaf
path, and touches a handful of pages. Writes reconstruct and re-validate the entire
database before touching anything. The gap is four orders of magnitude on the same
file, and it makes every write workload unusable at the paper scale.

Two constant-factor fixes have already landed (buffered page reads, and removing
two whole-file `List UInt8` conversions), taking an 11 MB write open from 5,394 ms
to 2,519 ms. They do not change the shape: the open is still O(database).

## Why the obvious fixes do not work

**A faster whole-database loader does not help.** A constructor that builds the
database directly from high-fanout pages was implemented and measured: 1,243 ms at
11 MB, which is exactly what the general decoder cost. `Core.Table` stores every
row in `rowTree`, so building one is O(rows) through any loader. Reverted; recorded
as disproved.

**Validating a fast path defeats the purpose.** The foreign-file boundary works by
running the verified executor and comparing. Here that means decoding the database,
which is the cost we are removing. Working rule 4 and the explicit non-goals rule
this out: the fast path has to be *proved*, not checked.

## Why it is an architecture change

The write side's correctness argument is founded on a materialized database:

- `CoreWidePageState.State` carries `database : Core.Database` and
  `tables_eq : tables.map TableState.table = database.tables`;
- `CoreWidePageState.TableState` carries `table : Core.Table` and
  `represents : Store.rows tree = table.rows`;
- `CoreWidePageDelta.executeInsert?` derives the physical delta by *running*
  `Core.execute` on that materialized database and proving the bytes refine it.

The physical write is correct because it agrees with the logical executor on a fully
decoded database. Removing the decode removes the reference the proof is stated
against. So the lazy path needs its own refinement, stated without a materialized
`Core.Database`.

## The design

### Idea

Do not avoid materializing rows. Avoid materializing *all* of them. An insert of one
row touches exactly one leaf page; decode only that leaf, insert into its row list,
re-encode that page, and leave every other page byte-identical.

The logical reference is then a table built from **one leaf's rows** — a handful,
independent of database size — rather than from the whole table. The existing
logical executor is still the reference, applied at leaf granularity, so we keep the
proof architecture and change only its scope.

### Scope of the first version

Deliberately narrow, so the refinement is provable and the fallback is total:

- exactly one supported statement in the batch;
- `INSERT` only (not `REPLACE`, `UPDATE`, `DELETE`);
- the target leaf has room, so no split, no interior-page change, no freelist
  change, no page-count change;
- the file carries the generated-image stamp, so the pages are known to have been
  written by this encoder.

Anything else returns `none` and takes the existing whole-database path. This is
the same shape as `CoreLazyFileEngine`: `none` is an optimization miss, never a
partial result.

### The obligation

Let `oldBytes` be the file, `p` the target leaf page, and `newBytes` the file with
only page `p` replaced. Write `denote` for the decoded table. The theorem to prove:

```text
locateLeaf oldBytes table key = some p
decodeLeaf oldBytes p = some rows
encodeLeaf (orderedInsert row rows) = some newPage
PageFit newPage
newBytes = replacePage oldBytes p newPage
------------------------------------------------------------
denote newBytes = orderedInsert row (denote oldBytes)
```

It decomposes into three parts, of which the first two already exist in some form:

1. **Frame.** Pages other than `p` are byte-identical, so their denoted rows are
   unchanged. This is the same property as the existing "every omitted post-state
   page is byte-identical to a complete pre-state page" accounting, read in the
   opposite direction.
2. **Concatenation.** A table's rows are the concatenation of its leaves' rows in
   page order. This is the defining property of the physical tree and is what
   `WidePageTree.Node.toList` computes.
3. **Routing.** `key` belongs in leaf `p` and in no other, from the interior
   separators on the path. This is the one genuinely new lemma: the read path
   *uses* routing to find candidates but does not need exclusivity, whereas a write
   does — inserting into the wrong leaf would still produce a well-formed file.

Routing exclusivity is the crux of the work — and investigating it surfaced a
blocker that changes what this task is. See the next section.

## The blocker: frame needs disjointness, and disjointness costs O(database)

The frame step requires that replacing page `p` leaves every *other* subtree's
denoted rows unchanged. That is true only if the other subtrees do not read page
`p` — i.e. subtrees occupy disjoint page sets. Without it the theorem is simply
false: if two children both pointed at `p`, rewriting `p` would change both.

Disjointness is **not derivable from the bytes on the root-to-leaf path**. Nothing
in a single path constrains what the rest of the file points at. The existing
disjointness lemma, `CoreChunkPageState.pageIds_disjoint_of_nodup`, is stated over
materialized `TableState`s and takes global page-ID uniqueness as a hypothesis; it
does not derive it from a page source.

Establishing disjointness from bytes means walking the whole tree — which is
precisely the O(database) validating open this design exists to remove. So:

**First conclusion, later shown wrong:** that the lazy write path is achievable
only by *assuming* the on-disk structure from the generated-image stamp instead of
checking it. See the next section — the check is cheap after all.

### Resolved: disjointness can be checked cheaply, so no trust change is needed

The reasoning above is wrong in one important step. It assumed that establishing
disjointness means walking the whole tree, and therefore costs O(database). It does
not: **disjointness is a property of page identities, and page identities live in
interior pages only.** Leaves are named by their parents, so every page id in a
table can be enumerated by reading interior pages alone — without decoding a single
row.

With real fanout, interior pages are a rounding error. Measured on the 1M-row,
583 MB file:

| | value |
|---|---:|
| total pages | 148,000 |
| interior pages | **563** (0.4%) |
| page ids enumerated by walking interiors only | 143,421 |
| duplicate page id found | none |
| **wall time for the whole check** | **80 ms** |
| one autocommit insert today | 143,671 ms |

So the premise the frame theorem needs can be *established*, not assumed, for about
80 ms — roughly 1,800x cheaper than the open it replaces, and about six times the
cost of a single read. The expensive part of today's open was never the structural
check; it was decoding every row to build `Core.Database`, which the structural
check does not require.

**Option 1's trust change is therefore unnecessary, and this design does not take
it.** The stamp keeps its current role: choosing a decoding strategy, not standing
in for verification. The three options below are retained only as a record of the
reasoning; the design proceeds with a checked structural premise.

### Why the trust change was considered, and rejected

### Why that is a decision rather than an implementation detail

The stamp is already in the trusted list, described there as "generated-image
provenance stamp (not cryptographic authentication)". Today it is used only to
choose a decoding strategy; the structure is then *checked*, and that check is the
144-second cost. Making it load-bearing for structural soundness means:

- a stamped file whose interior pages were corrupted or tampered with would be
  written to without detection, where today it is caught and rejected;
- the guarantee changes from "the engine verifies what it opens" to "the engine
  trusts files carrying its own stamp";
- the trusted computing base does not grow in *count*, but one existing entry
  becomes far more load-bearing, and the TCB's size and weight is the project's
  headline property.

The explicit non-goals of the paper programme include "replacing the fail-closed
foreign-file validation boundary with unchecked trust". This is not that boundary —
it concerns our own generated files, not foreign ones — but it is close enough that
it must be an explicit, recorded decision rather than something absorbed into an
optimization.

### The three options

1. **Trust the stamp for structure.** Gets the full win: one insert at 1M rows goes
   from 144 s to the order of a read. Requires the trust change above, documented in
   `docs/TRUST.md`, and honesty about it in the paper.
2. **Keep checking, and make the check cheap.** Amortize disjointness across a
   session rather than per statement: check once per connection and cache it. This
   does nothing for the single-statement case that item 3's acceptance test
   measures, but it removes the cost from multi-statement write sessions, which is
   what the benchmark and any real application actually do.
3. **Persist the checked structure.** Store the validated page-ID set in the file
   or a sidecar so a later open can trust it without rewalking. This trades trust
   for a new on-disk invariant and a new way for the file to be internally
   inconsistent, and it breaks byte-compatibility if stored in the main file.

Option 2 is the only one that needs no trust change, and it is strictly weaker than
what the acceptance test asks for. Option 1 is what the design above assumes.
**This needs deciding before the implementation is worth writing**, because the
refinement theorem is stated differently in each case.

### Module layout

New module `SQLeanite/CoreLazyWrite.lean`, additive:

- `locateLeafPath? : PageSource → Schema → key → Option LeafPath` — root-to-leaf
  descent recording separators, so exclusivity is available as a proof, not
  re-derived;
- `insertIntoLeaf? : LeafPath → Row → Option LeafWrite` — decode the leaf, insert,
  re-encode, and require `PageFit`;
- `LeafWrite.refines : denote (apply w bytes) = orderedInsert row (denote bytes)` —
  the theorem above;
- `execute? : Paths → Statement → IO (Option Result)` — the engine entry point,
  mirroring `CoreLazyFileEngine.execute?`.

Nothing existing is modified except one branch in `Main.lean`'s batch dispatch,
which tries `CoreLazyWrite.execute?` before `CoreFileEngine.reopen`. Every current
theorem stays true and untouched, which is the point of doing it additively: an
in-place change would leave `executeText_commit_crash_atomic` — the project's
headline claim — broken partway through.

### Durability

The lazy path must reuse the existing journal protocol unchanged: journal the
pre-image of page `p`, sync, write `p`, sync, unlink. Because exactly one page
changes, the existing crash-atomicity theorem over an arbitrary exact page-write
list applies directly; no new crash reasoning is required. This is the reason for
excluding splits in the first version — a split changes page count and freelist
state, which is a different crash shape.

### Acceptance

- a single-row insert into a 1 MB and an 11 MB database cost about the same;
- one insert at 1M rows drops from 144 s to the order of a read (tens of ms);
- 151 tests, the differential suite, the live-path audit and the verification audit
  all stay green;
- zero `sorry`, and the trusted-binding count does not rise.

### Risks

- **Routing exclusivity is new proof work** and is the item most likely to
  overrun. If it does, the executable is worthless: an unproved fast write path is
  not acceptable, and there is no cheap validation to fall back on.
- **Zero-`sorry` is a hard gate**, so a partially proved module cannot land at all.
  The work either completes or is not committed.
- The narrow scope means `INSERT` into a full leaf, and all of
  `REPLACE`/`UPDATE`/`DELETE`, keep the old cost until follow-up work widens it.


## Implementation plan and attempt log (2026-08-16)

Landed and sound: `SQLeanite/CoreLazyWrite.lean` with `subtreePages` and
`mem_subtreePages_self`. Everything below is the remaining work, in order, with
what was learned attempting it.

### Phase 1 — leaf-read agreement (the blocker)

`CoreDecode.decodeRowsFrom` takes the page source and follows overflow chains
through `decodeRowsByPointersFrom` / `decodePackedRowCellsFrom`, so a subtree's
decoded rows can depend on pages `subtreePages` does not name.

**Do not fix this by enumerating overflow pages.** Predicting which pages the
decoder reads means reimplementing its cell parsing, and an enumeration that
disagrees with the decoder produces a frame lemma that compiles and is false.

Discharge it with a *counting* check instead: if the enumerated tree pages, plus
page one, plus the freelist, account for every page in the file, then no overflow
page exists and leaf reads cannot leave the enumeration. The check is cheap — the
enumeration already costs about 80 ms at 1M rows — and it is a check, so the
fallback stays total.

### Phase 2 — the frame lemma

State it as a *source congruence*, not over `CorePageSource.write` directly:

```lean
theorem decodeSubtreeRowsFrom_congr (schema) (left right : PageSource)
    (leafAgrees : ∀ page, decodeRowsFrom schema left page
      = decodeRowsFrom schema right page) :
    subtreePages left fuel pageNumber = some pageList →
    (∀ p ∈ pageList, left.readPage p = right.readPage p) →
    decodeSubtreeRowsFrom schema left fuel pageNumber
      = decodeSubtreeRowsFrom schema right fuel pageNumber
```

The `write` case is then a corollary via the primitives that already exist in
`CorePageSource`: `readPage_write_same`, `readPage_write_other`, `applyWrites`.
Stating it over `write` directly drags in a bounds obligation — `write` returns
`none` above `max source.pageCount (pageWrite.pageId + 1)` — which the congruence
form avoids entirely.

Two practical notes from the attempt:

- **`subtreePages` must be written with explicit `match`, not `do`.** With
  do-notation the hypothesis is an `Option` bind that `split` cannot see through,
  and neither `dsimp`, `Option.bind_some` nor `Option.some_bind` reduces it. The
  committed definition already uses explicit matches for this reason.
- The induction's interior case needs *child pages are among the parent's*, which
  comes from `pageList = pageNumber :: nested.flatten` plus membership reasoning
  through `List.mapM`. `subtreePages_children` is the lemma to write first; the
  induction is straightforward once it exists.

### Phase 3 — routing exclusivity

That the key belongs to leaf `p` and no other, from the interior separators along
the descent. `locateLeafPath?` should record the separators as it descends so
exclusivity is available as a proof rather than re-derived. This is the one part
with no existing analogue: the read path *uses* routing to find candidates but
never needs exclusivity, whereas a write does — inserting into the wrong leaf still
produces a well-formed file.

### Phase 4 — engine

`CoreLazyWrite.execute?` mirroring `CoreLazyFileEngine.execute?`, tried from
`Main.lean` before `CoreFileEngine.reopen`, with `none` meaning "optimization
miss" and never a partial result. Journal the single page's pre-image, sync, write,
sync, unlink; because exactly one page changes, the existing crash-atomicity
theorem over an arbitrary exact page-write list applies unchanged.

### Status: the refinement is proved (2026-08-16)

`SQLeanite/CoreLazyWrite.lean` is sorry-free. `insertPlan_refines` depends only on
`propext`, `Classical.choice` and `Quot.sound`.

| phase | outcome |
|---|---|
| 1 overflow enumeration | discharged as `LeafInline`, transported between sources by `LeafInline_congr` |
| 2 frame | `decodeSubtreeRowsFrom_congr`, stated as a source congruence with a page-indexed leaf premise |
| 3 routing | `TreeSound` + `locateLeaf_routedSplit`; `orderedUpsert_routedSplit` supplies the arithmetic |
| 4 engine | `executeInsert?`, behind an explicit opt-in -- see below |

Frame and routing had to become **one** induction, `locateLeaf_write_refines`, not
two lemmas composed. The frame step needs to know which child owns the written page,
and that is exactly what the descent decides; splitting them leaves the frame half
with no way to name the owner.

Three further corrections the proofs forced:

- `locateLeaf?` treated any page with undecodable separators as a leaf, so a corrupt
  interior page could have been rewritten as one. It now fails closed.
- The separator contract has to be stated in `treeKey` space. Rowids are biased by a
  midpoint before being compared, so bounding `rowid.value` by a separator compares
  across two different spaces. `Core.Row.treeKey_lt_iff` converts where needed.
- `WellFormedTree.childrenDisjoint` was not inhabitable as written -- it quantified
  over arbitrary child lists, so `[c, c]` forced the subtree empty. Replaced by
  `TreeDisjoint`, stated recursively in the shape routing consumes.

### What is not done: runtime checking of the premises

The refinement is *conditional* on `WellFormedTree`. Nothing checks those premises at
open time yet, so the CLI reaches the page-local path only under
`SQLEANITE_PAGE_LOCAL_WRITES=1`. Making it the default needs decidable checkers for
`TreeSound` and `TreeDisjoint` plus soundness proofs; the measurements below show
both are cheap to compute (1,720 ms at 1M rows for the full per-leaf monotonicity
scan the premise actually requires — see the correction at the end of this file), but
computing them is not the same as proving the checker implies the proposition.

### Measured

With the opt-in set, a single insert is flat in database size:

| rows | size | one insert |
|---:|---:|---:|
| 5,000 | <1 MB | 30 ms |
| 50,000 | <1 MB | 35 ms |
| 200,000 | 3 MB | 30 ms |

against 992 / 5,394 ms before, and 143,671 ms for one insert at 1M rows.
`PRAGMA integrity_check` is clean and the row count matches.

The path applies only when the target leaf has room. With 512-byte rows a leaf holds
eight, so most inserts need a split and fall back to the whole-database path at the
old cost -- the scope limit stated above, now measured rather than assumed.


## Cost decomposition of the open (2026-08-16)

Fitting two independent experiments — same file size with different row counts, and
same row count with different widths — gives the open cost as:

```
open ≈ 180 ms per MB  +  21 µs per row
```

| shape | rows | size | open |
|---|---:|---:|---:|
| 512-byte rows | 20,000 | 11 MB | 2,510 ms |
| 56-byte rows | 160,000 | 15 MB | 6,869 ms |
| 64-byte rows | 20,000 | 2 MB | 836 ms |

At the YCSB shape the per-MB term is 83% of the cost. 180 ms/MB is 180 ns per
byte, which is one to two orders of magnitude slower than a byte parse should be,
and it is spent turning page bytes into `Core.Row` values whose TEXT payloads are
`List UInt8`.

That gives a **second, independent route to item 3's acceptance**, if the lazy write
path proves too slow to land: decode from `ByteArray` rather than `List UInt8`.
It does not change the asymptotics — the open stays O(database) — so it does not
meet the acceptance criterion by itself, but it attacks the same 83% and is
mechanical rather than novel proof work. The two routes compose: the lazy path
removes the O(database) term, and a ByteArray decoder shrinks what remains for the
fallback path that foreign files still take.


## The routing premise is checkable too (measured 2026-08-16)

Routing correctness needs more than page disjointness: it needs the separators to be
trustworthy, i.e. the leaves genuinely in key order. That is what `RoutedSplit`
demands and what `WellFormedTree.rowsOrdered` supplies.

The concern was that global key ordering could only be established by decoding every
row -- exactly the cost being removed. It cannot, and it does not have to be: keys
live in the cell headers, so ordering across the whole table is verifiable by reading
each leaf and parsing cell headers, without decoding a single row or touching a
payload.

### Correction (2026-08-16): first/last is not the premise

The original version of this section measured each leaf's **first and last** cell and
called the result the structural check. That is weaker than the premise it was cited
for. First/last bounds every key in a leaf *only if the leaf is internally sorted*,
and internal leaf ordering is one of the things `TreeSound` asserts rather than
something a checker may assume. A leaf whose cells are `[5, 99, 7]` passes a
first/last scan against neighbours holding `[1..4]` and `[100..]`, yet routing a key
of 8 into it and re-encoding `orderedUpsert` would not preserve the decoded order the
refinement's conclusion is stated over.

So the honest checker parses **every** cell header of every leaf. That is still a
header parse, not a row decode: no payload is read, no overflow chain is chased, and
no `Core.Row` is built.

### Re-measured with full per-leaf monotonicity

`scripts/structural-check-census.py` makes this reproducible; the earlier numbers had
no tool behind them. Median of three warm passes over a 1,000,000-row, 582.41 MB
C-SQLite-written file of the YCSB shape (`usertable(ycsb_key TEXT PRIMARY KEY,
field0 TEXT)`, 512-byte fields, 149,098 pages of 4,096 bytes, 359 interior pages,
142,858 leaves):

| step | cost |
|---|---:|
| tree-order walk of interior pages | 322 ms |
| first/last cell of all 142,858 leaves (weak) | 815 ms |
| **every cell of every leaf (the `TreeSound` shape)** | **1,398 ms** |
| total, endpoints only (what 653 ms measured) | 1,136 ms |
| **total structural check, full monotonicity** | **1,720 ms** |
| ordering violations found, either scan | **0** |
| one autocommit insert at this scale today | 143,671 ms |

Two things changed against the superseded row. The check is **1,720 ms, not 653 ms**:
about 1.6x of that is the stronger scan, and the rest is that these numbers come from
an instrumented Python reader on this machine rather than from the earlier untooled
measurement, so treat the *ratio* as the durable claim and the absolute as
machine-specific. The ratio: both premises the refinement needs -- disjointness and
ordering -- are **checked** in about 1.7 s, some **84x** cheaper than the
whole-database open they replace, and paid once per open rather than per statement.
Not the 220x previously claimed, and 220x was for the weaker scan.

No trust change, and the generated-image stamp keeps its existing weaker role. Note
also that a Lean checker with a soundness theorem is what the engine would actually
need; this tool measures the cost of that obligation, it does not discharge it.

Three implementation notes, all mistakes made while measuring this and worth not
repeating: leaves must be visited in *tree order* (a DFS through interior children),
not page-number order, since page numbering does not follow key order; leaf cell
pointers start at byte 8, where interior pages start at 12; and a one-cell leaf must
contribute one key to the endpoint scan rather than the same key twice, or the strict
comparison fires on `key <= key`. Each of the three makes the check report violations
that are not in the file, which reads as a corrupt database rather than as a broken
checker. The third one actually fired during this re-measurement: the endpoint scan
reported exactly one violation that the full scan did not, and it was the checker.
