# Final gap-closing plan

Scope: what is left before a first paper submission. Written 2026-08-16 against
commit `b21cd8e`, from a measured audit of the tree rather than from the other
plan documents, several of which are stale (see workstream D).

This plan **closes gaps**. It adds no SQL surface, no file features, and no
performance work. Where a gap can be closed by stating a boundary precisely
instead of proving past it, that is the chosen resolution.

## Decisions taken

1. **The claim is a verified core with a documented executable boundary**, not a
   verified binary. This is the decision that shapes everything below: the
   unproved IO plumbing in the cold read path becomes a *boundary-documentation*
   deliverable (workstream C) rather than a proof obligation.
2. **The generated-image stamp stays load-bearing** for cold missing-key and
   certified-index results, as it is today. `docs/TRUST.md` already discloses
   it, says it is not a MAC, and names the threat model. No work.
3. **Priority order: POPL'10 parity first, byte compatibility second, FSCQ-style
   durability third.** Durability is nice to have and is already largely in
   place; it gets no new proof work.

Default taken in the absence of a decision, flagged in "Open decisions": the
page-local write path is presented as **proved but not deployed**.

## Measured starting point

| | |
|---|---:|
| theorems / headline theorems | 2,011 / 872 |
| `sorry`, project `axiom`, `unsafe`, `partial def`, `native_decide` | 0 |
| opaque host bindings | 9 (8 syscalls + process liveness) |
| executable tests | 151 |
| Core differential cases | 13 (10 SQL + 3 reverse-direction page sizes) |
| upstream-adapted cases | 11 supported, 2 declared unsupported |
| Lean mutations detected | 21 / 21 |
| `reproduce-all` QUICK | exit 0 |

---

## Workstream A — POPL'10 parity (priority 1)

Closer to done than the plan documents suggest. `RelationalAlgebra.permute_eval`,
`permute_symm_eval` and `innerJoin_true_eval` all exist; `QueryCost.lean` carries
a per-rewrite cost theorem for every live rewrite plus `optimizePlan_cost_le`;
`CoreReadSemantics.lean` bridges the live executor to the denotation for query,
join, group, count, sum, extreme and compound reads. Two gates already pass in
`scripts/live-path-check.sh`.

### A1. Connect the parity witnesses to the live executor — the real gap

`CoreReadSemantics.lean` never mentions `permute_eval` or `innerJoin_true_eval`.
`RelationalAlgebra.lean` is imported only by `CoreReadSemantics` and
`ProofAxioms`, and the live-path gate checks only that the names appear in
`ProofAxioms` — that they are *audited*, not that they are *reached*.

So today "we have their permutation and product primitives" is a true statement
about a standalone algebra module, not about the shipped read path. That is the
softest point in the highest-priority claim and a reviewer will find it.

- **Permutation: prove the bridge.** One lemma: Core's projection with a
  permuted column list denotes `RelationalAlgebra.permute` of the unpermuted
  projection. This turns "we have a permutation primitive" into "the live
  projection *is* their permutation on the denotation".
- **Product: state the direction, do not prove more.**
  `innerJoin_true_eval` already says product is the constant-true special case
  of our inner join. POPL'10 derive join from product; we go the other way.
  Say so in one sentence rather than manufacturing a primitive we do not have.

*Acceptance:* a named theorem in `CoreReadSemantics.lean` for permutation, and a
live-path assertion that it is reached, not merely audited.

### A2. Emit the parity table as an artifact

Six operators → our theorem names → parity or superset. Generated from
`ProofAxioms.lean` by `scripts/lean-manifest.sh` so it cannot drift.

| POPL'10 primitive | our witness | status |
|---|---|---|
| selection | `CoreReadSemantics.execute_query_denotes` | parity |
| projection | same | parity |
| permutation | A1's new bridge lemma | parity *(after A1)* |
| union | compound denotation | parity |
| difference | compound denotation | parity |
| cartesian product | `RelationalAlgebra.innerJoin_true_eval` | parity, derived in the opposite direction |

### A3. Confirm the cost gate is exhaustive

`live-path-check` asserts the live optimizer root is restricted to proved
cost-safe rewrites. Verify this is exhaustive over the live rewrite set rather
than a spot check, and record the count. `filterFusion_not_unconditionally_cost_safe`
is a negative result and should be *featured*: POPL'10 proved *several*
transformations non-cost-increasing; we prove one is not, and gate it.

### A4. State set-versus-bag once, prominently

Their relations are finite sets (`FSetInterface`); no duplicates, no NULL logic.
Ours is a bag with SQLite three-valued predicates. This is a strictly harder
target and must be stated as an improvement, never as parity. It belongs in the
claim section, not per-operator.

**Estimate:** A1 1–3 days; A2 half a day; A3 half a day; A4 hours.

---

## Workstream B — byte compatibility (priority 2)

The headline claim with no prior art, and its evidence base is the thinnest part
of the project.

### B1. Widen the reverse direction (C writes, we read) — the main gap

Today this is **three cases**: one table, one index, 200 rows, at page sizes
1024 / 8192 / 65536. Everything else in the differential arm is our own writes.

`plan.md` claims the read path already accepts overflow chains, multi-page
interior nodes, freelists after large deletes, post-`VACUUM` files,
`auto_vacuum`, REAL and BLOB, and WAL — but only the page-size trio is under
continuous test. Untested acceptance is not evidence.

Build a C-written corpus crossing **file feature × page size**: overflow rows
(9 KB), multi-level interior nodes, freelist after bulk delete, post-`VACUUM`,
`auto_vacuum`, REAL, BLOB, NULLs, composite shapes, WAL. Cheap to generate with
`sqlite3`; each case is read by both engines and compared.

*Acceptance:* the differential arm reports a feature × page-size matrix, and
every cell is pass or an explicit declared-unsupported.

### B2. Strengthen the forward direction (we write, C reads)

Currently two live-path assertions plus `integrity_check`. Extend to: for every
workload shape, C SQLite runs `PRAGMA integrity_check` **and** returns identical
contents. Cheap, and it is the direction reviewers care about most.

### B3. Write side emits 4096 only — state the asterisk

`PhysicalCodec.pageSize = 4096` is threaded through sixteen modules and baked
into type signatures. Parameterizing it is surface-widening in effect. Decision:
**state the asymmetry** — we read four page sizes and write one — rather than
close it.

### B4. `WITHOUT ROWID` must fail closed, and be tested doing so

Declared out of scope. Add a test that it is rejected as an ordinary
diagnostic, so "unsupported" is a checked property rather than an omission.

### B5. Emit an accepted / rejected / untested feature table

Generated from the corpus, in `docs/`. This is the artifact that makes the
byte-compatibility claim auditable.

**Estimate:** B1 2–3 days; B2 1 day; B3 hours; B4 hours; B5 half a day.

---

## Workstream C — the executable boundary document

This is what the chosen claim buys: instead of proving the cold read path, state
exactly where the proofs stop, and make that statement drift-proof.

### C1. Name the unproved shipped paths

- `CoreLazyFileEngine` — **0 theorems, 0 `ProofAxioms` entries**, tried first for
  every read in `Main.lean`.
- Its four IO lookups in `CoreFileAdapter` — `lookupPrimaryRowDecision`,
  `lookupGeneratedPrimaryRange`, `lookupGeneratedIndexCandidatesWith`,
  `lookupGeneratedOrderedPrefix` — return plain `IndexLookup { candidates,
  pagesRead }`, not the proof-carrying `CertifiedCandidates { candidates, exact }`
  the warm path uses.
- `Main.lean`'s shell, already disclosed.

### C2. State the pure/IO seam precisely

The honest form, which is much stronger than "the fast path is unproved":

> The page traversal itself is proved exact against the decoded abstraction and
> against the encoder — `lookupIndexRangeFrom_refines_full_decode`,
> `lookupTableRangeFrom_decodeAbstract_exact`, `lookupIndexValueFrom_certified_exact`,
> and the promoted-key index refinement. The optimizer is proved preserving
> (`optimize_eval`). What is not covered by a theorem is the IO wrapper that
> supplies those functions with the file's pages, so the composition down to
> `Core.execute` is asserted by the live-path audit rather than proved.
> `CoreFileAdapter.byteArrayPageSource_eq_storageImage` is the one place this
> bridge exists, for the pure source; `preadPageSource` and `filePageSourceFor`
> have no counterpart.

Also record the mitigations, because they are real: a point-lookup hit
self-checks `row.rowid = rowid && row.WellFormed schema`; index lookups locally
validate every resolved rowid/value link; misses are admitted only under the
stamp.

### C3. Make the boundary machine-emitted

Extend `scripts/lean-manifest.sh` to classify every shipped entry point as
theorem-covered or boundary-listed, and emit the table.

### C4. Add the anti-drift gate

A `live-path-check` assertion that every shipped read/write entry point is
either covered by a named theorem or present in the boundary list. New unproved
code then fails the audit instead of arriving silently. This is the honest
mechanical meaning of "documented executable boundary".

**Estimate:** C1 half a day; C2 half a day; C3 1 day; C4 half a day.

### C5. Optional upgrade, not scheduled

A general "IO page source faithfully reads the file" lemma, mirroring
`byteArrayPageSource_eq_storageImage`, would let the cold read path compose to
`Core.execute` and would move `CoreLazyFileEngine` from boundary-listed to
theorem-covered. **2–4 days for the lemma, 3–7 days for the four compositions.**
Not required by the chosen claim. Promote only if the schedule allows.

---

## Workstream D — claim accuracy

Cheap, and reviewers do check these.

- `plan.md` §3: says 149 tests, seven bindings, 1,292 theorems. Actual: **151,
  nine, 2,011**.
- `plan.md` §4: benchmark table dated 2026-08-13 at `93e611223c`, superseded by
  PAPER_PLAN's 2026-08-16 measurements. Refresh or mark superseded — do not
  leave two live tables.
- `plan.md` item 7: says non-4096 page sizes are rejected. **Reads accept 1024,
  8192 and 65536**; the differential arm covers all three. Mark the read half
  done and fold the write half into B3.
- `plan.md` item 8: acceptance is "deleted, *or* retained solely for the
  foreign-file case with a comment and a live-path assertion". That assertion
  exists and passes (`uncertified candidate comparison is confined to foreign
  files`). Verify and mark done.
- `docs/LAZY_WRITE_DESIGN.md`: the 653 ms structural check reads each leaf's
  **first and last** cell. That bounds the rest only if the leaf is internally
  sorted, so it is weaker than the `TreeSound` premise it is cited for. Restate,
  and re-measure with full per-leaf key monotonicity.
- Page-local write path: present as **proved but not deployed** (`insertPlan_refines`,
  behind `SQLEANITE_PAGE_LOCAL_WRITES=1`, premises unchecked at runtime, engine
  not linked to the theorem). See "Open decisions".

**Estimate:** hours, all together, except the LAZY_WRITE re-measure (half a day).

---

## Workstream E — artifact

- One clean **full** `reproduce-all` run. Only QUICK has been verified; the C
  mutation arm, crash and power-loss sweeps, scaling curves, the workload
  benchmark and YCSB are all skipped in that mode.
- Snapshot the theorem/TCB/LOC manifest and proof-latency numbers for the paper.
- Report YCSB beside the twelve public workloads, with the write-heavy A/B/F
  ratios (9.9–13.3x) stated plainly rather than buried.

**Estimate:** 1 day, mostly wall-clock, plus whatever the full run surfaces.

---

## Workstream F — FSCQ-style durability (priority 3, nice to have)

Already in place: `executeText_commit_crash_atomic` and its family, the
localized-commit crash theorems, crash fault injection with stock SQLite as a
control, and power-loss injection with a mutation control that *must* tear.
That is the FSCQ-shaped result.

**No new proof work.** Two statements only:

- the durability claim is conditional on `SyscallVFS.Contract`, which stays in
  the documented TCB;
- FSCQ's evaluation (xv6 build, mail server, vs ext4) is filesystem-shaped and
  does not transfer to a database. The FSCQ comparison is about the *durability
  theorem*; YCSB is about *performance comparability*. Do not conflate them.

**Estimate:** hours.

---

## Workstream G — close the write-side semantic gap (priority 3)

Added 2026-08-16 after a second audit. The read side has a denotational story
(`CoreReadSemantics.lean`: `execute_query_denotes`, `execute_join_denotes`, and
the rest). The write side has no analogue, and the two never meet.

### G1. Membership iff for `orderedUpsert`

`mem_orderedUpsert` is forward only: `candidate ∈ orderedUpsert row rows →
candidate = row ∨ candidate ∈ rows`. Missing the converse — that `row` is in the
result, and that non-colliding rows are retained. Nothing needs it today; G2 and
G3 do. **Hours.**

### G2. Rowid freshness in the insert postcondition

Prerequisite for G3 and G4. The insert path knows the rowid is fresh -- see the
private `Table.findRowid?_fresh_of_not_isSome` -- but does not expose it in the
postcondition, so no downstream theorem can use it. **~1 day.**

### G3. A bag-level insert theorem

New `CoreWriteSemantics.lean`, mirroring `CoreReadSemantics.lean`:
`⟦after⟧ = ⟦before⟧ ⊎ {row}` over `KRelation`. Today `Core.orderedUpsert` serves
as both specification and implementation -- it is a list function with
insertion-order semantics -- so there is no statement of what an insert *means*
that is independent of how it is performed. **2–4 days.**

### G4. Close the loop: write → bytes → reopen → read

The theorem that a row inserted by the write path is the row a later read
observes, *through the encoded bytes and a reopen*. This is rated higher here
than in the source list, because it is close to the statement a
byte-compatibility paper actually wants, and because PAPER_PLAN's milestone 5
("end-to-end composition") currently has two headline theorems and nothing
crossing the write/read seam. The reopen leg is the hard part: it crosses
`encodeBulk`/`decode`, so it should compose the existing whole-image inverse
rather than re-prove it. **3–5 days.**

*Acceptance:* one named theorem, reached from a live write text and a live read
text, registered in `ProofAxioms.lean` and pinned by `live-path-check.sh`.

---

## Workstream H — progress (priority 3)

Every headline theorem is conditional on success. `executeText_commit_crash_atomic`
takes `success : CoreSQL.execute state text = .ok (next, [result])` as a
hypothesis; there is no theorem anywhere that a valid statement *succeeds*. This
is the standard objection to a verified system and it currently lands.

The subtlety the work has to respect: `execute` legitimately fails -- duplicate
primary key, type error, missing table, value out of bounds. So the theorem is
not totality. It is:

> a supported statement, on a well-formed state, whose stated preconditions hold
> (schema conformance, no key collision, values in range), returns `.ok`.

Characterizing those failure modes *is* the work. Scope it to `INSERT` and
`SELECT` in the pure core; do not attempt the whole command set for a first
submission. **3–5 days.**

*Acceptance:* a progress theorem for insert and for select, and a stated list of
the failure modes each one excludes.

---

## Workstream I — assumption hygiene (priority 4)

### I1. `UTF8Roundtrips` stays a documented assumption

`CoreDecode.UTF8Roundtrips : ∀ value : String, TextRoundtrips value` is a
hypothesis on `decode_encodeBulk` and 64 other sites. It exists because the Lean
standard library exposes no theorem for its own UTF-8 implementation. `TRUST.md`
already discloses it.

**Decision: do not thread a per-value witness through 65 sites for a first
submission.** But state one thing in the paper that costs nothing: `TextRoundtrips
value` has a `Decidable` instance, so the universal law *could* be replaced by a
per-string check at the boundary. Naming that turns an assumption into a
disclosed, checkable one. **Hours.**

### I2. Correction to record

`PostImageCertificate` is *not* an assumed decoder equation. It is an inductive
with five constructive alternatives and the explicit comment "There is
deliberately no constructor accepting an opaque decoder equation"; the live
localized path uses `.components`/`.ordinary`, which `CoreDurability` builds from
the live writer. Only the `bulk`/`padded`/`wideBulk` constructors mention
`encodeBulk … = some image`. Do not list this as an assumption; it is discharged.

---

## Explicitly not doing

- `WITHOUT ROWID`, subqueries, views, triggers, `ALTER`, savepoints, `ATTACH`,
  multiple aggregates per projection, column-to-column `WHERE`.
- Parameterizing the write-side page size.
- Any performance work. Current numbers are the reported numbers.
- Runtime checkers for the page-local write premises (`TreeSound`,
  `TreeDisjoint`), and linking `commitLocalized` to `insertPlan_refines`.
  1–2 weeks and 2–4 days respectively; not needed for a non-deployed path.
  This is the item to pick up first if the write path is ever to ship enabled.
- Threading a checked `TextRoundtrips` witness through the 65 `UTF8Roundtrips`
  sites. See I1: disclose and note decidability instead.
- Progress for the full command set. H is scoped to insert and select.
- The IO↔pure source lemma (C5), unless promoted.
- General parser correctness. `parseCertified_agrees_parse` covers admitted
  ASTs, which is the same relative standard POPL'10 met against their PEG
  grammar. State the scope; do not widen it.

---

## Order

1. **D** — half a day, and it stops the other documents contradicting the paper.
2. **A** — the top-priority claim, and A1 is its weakest joint.
3. **B** — the claim with no prior art and the thinnest evidence.
4. **C** — depends on nothing; can run in parallel with B.
5. **H** — the standard reviewer objection; independent of everything else.
6. **G** — G1 is hours and can land any time; G2→G3→G4 are sequential.
7. **F**, **I** — hours each.
8. **E** — last, because it snapshots everything above.

Rough total: **four to five weeks** of focused work with B/C and G/H
parallelizable — roughly double the original estimate, which covered only A–F.
If the schedule will not take that, cut in this order: G3 and G4 first (they
strengthen the story but nothing currently claimed depends on them), then H
(disclose partial correctness instead of fixing it), then B1 down to a smaller
matrix. Do not cut A or D.

A note on these estimates: mine ran consistently low during the work that
produced this plan. I called the last refinement "plumbing" and it took a full
session and three false theorem statements. Treat every number here as
optimistic, and treat A1 and B1 as the two most likely to overrun.

---

## Open decisions

1. **Page-local write path framing.** Default taken: present as proved but not
   deployed, with the two gaps named. Alternatives: cut it from the paper
   entirely (the write-open story then reverts to "improved 2.2x, still
   O(database)"), or actually gate it (1–2 weeks). The proof is the interesting
   part and it costs nothing to include honestly, which is why the default is
   what it is.
2. **Venue and deadline**, which decides whether C5 gets promoted.
3. **B1 corpus breadth.** The feature × page-size matrix could be a dozen cases
   or fifty. More is better evidence and more wall-clock in `reproduce-all`.
   Default: a dozen, chosen to cover each named file feature once at 4096 and
   each page size once at a non-trivial shape.
