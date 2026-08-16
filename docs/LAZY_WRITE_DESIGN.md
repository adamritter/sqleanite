# Design: a page-local write path

Status: design agreed, implementation in progress. This closes open-work item 3 in
`PAPER_PLAN.md`.

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
in `PAPER_PLAN.md` as disproved.

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

Routing exclusivity is the crux of the work.

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
