# SQLite C-to-Lean port: scalar values, text/blob functions and column affinity

This is an incremental port, **not a complete SQLite implementation**. The
reference is SQLite **3.53.4**, checkout `b09c88c14082339b66c7b7158d609a771e64ca69`
in the adjacent `sqlite/` directory. All implementation changes in this step
are Lean. The existing OS bindings are unchanged; the engine does not call C
SQLite. C SQLite is used only as an independent test oracle.

## Accepted compatibility target

The user-confirmed target is SQLite **3.53.4 SQL behavior, database file format
and WAL file format**. The C API and loadable-extension ABI are outside this
target. This target is not yet achieved: the checkpoints below measure specific
implemented subsets, and known rejections and mismatches remain explicit.

## Source correspondence and production use

| SQLite source | Lean implementation | Behavior ported |
| --- | --- | --- |
| `util.c`: `sqlite3Multiply128`, `sqlite3Multiply160`, `powerOfTen` | `SQLite/FloatCodec.lean` | Wide products, original scaling tables and normalization |
| `util.c`: `sqlite3Fp2Convert10`, `sqlite3Fp10Convert2`, `sqlite3FpDecode` | `SQLite/FloatCodec.lean` | Binary/decimal conversion, default 17-digit rounding and round-trip shortening |
| `printf.c`: `%!.17g`; `vdbemem.c`: `vdbeMemRenderNum` | `SQLite/FloatCodec.render`, `Value.lean` | REAL text, decimal/exponent notation, exponent padding, signed infinities and zero |
| `util.c`: `sqlite3AtoF`, `sqlite3Atoi64` | `Value.parseDecimal?`, `SQLite/Numeric.lean` | Bounded decimal mantissa, exponent adjustment, numeric prefixes, signed saturation, ASCII whitespace, embedded NUL distinction |
| `vdbemem.c`: `sqlite3VdbeIntValue`, `sqlite3RealToI64`, `sqlite3VdbeMemNumerify`, `sqlite3VdbeMemCast` | `SQLite/Numeric.lean`, `SQLite/Scalar.cast` | INTEGER/REAL/NUMERIC/TEXT/BLOB conversions, including CAST versus arithmetic differences |
| `vdbe.c`: `computeNumericType`, arithmetic, bit and comparison opcodes | `SQLite/Scalar.lean` | INTEGER fast path, REAL fallback, overflow, NULL, divide by zero, signed remainder, saturating shift counts |
| `expr.c`: comparison affinity, constant AND/OR simplification | `SQLite/Scalar.lean` | CAST expression affinity, lossless comparison conversion, constant boolean error suppression |
| `build.c`: `sqlite3AffinityType`, declared type dequoting | `SQLite/Type.lean`, `CoreSQL.declaredTypeName` | Shared type-name precedence for CAST and stored columns |
| `vdbe.c`: `applyNumericAffinity`, `alsoAnInt`, `applyAffinity`; `vdbemem.c`: `sqlite3VdbeIntegerAffinity` | `SQLite/Numeric.applyAffinity`, `SQLite/PhysicalAffinity.lean` | Lossless numeric conversion, integer endpoint handling, write and comparison affinity |
| `vdbe.c`: `OP_RealAffinity` | `PhysicalAffinity.realRead`, `CoreRecord.decodeRowFields` | Reconstruct logical REAL values from native SQLite integer serial types |
| `expr.c`: `TK_UMINUS`, `codeReal` | `SQLite/Scalar.evalFuel` | Preserve negative zero for negated REAL literals; use subtraction for other operands |
| `func.c`: `substr`/`substring`, `instr`, trim variants, `replace`, `concat`/`concat_ws`, `hex`/`unhex`, `quote`, `char`, `unicode`, `zeroblob`, `sign`, scalar `min`/`max` | `SQLite/Text.lean`, `SQLite/Scalar.builtin` | Character versus byte indexing, negative offsets/counts, embedded NUL rules, arity, NULL behavior, and result storage classes |
| `utf.c`: `sqlite3Utf8Read` | `SQLite/Text.firstCodepoint` | `unicode` over raw BLOB bytes, invalid sequences and unsigned 32-bit accumulation |
| `func.c`: `typeof`, `abs`, `length`, `octet_length`, `upper`, `lower`, `nullif` | `SQLite/Scalar.builtin` | Arity checks, overflow error, UTF-8 character/byte distinction, ASCII-only folding |
| `expr.c`: conditional expression generation | `SQLite/Scalar.evalFuel` | Lazy CASE, coalesce, ifnull and variadic iif/if evaluation |
| `select.c`: row-dependent projection | `CoreExpr.lean`, `Scalar.evalWith`, `CoreSQL.executeExpressionSelect` | Explicit row bindings and column affinity, scalar expressions, in-place star expansion, projected DISTINCT and existing source-column ordering |
| `select.c`: SELECT without FROM | `CoreSQL.constantRow` | One implicit input row, WHERE, DISTINCT, LIMIT/OFFSET and existing compound-query composition |

Wide multiplication uses Lean natural numbers instead of C intrinsics. This
preserves the high/low word computations without handwritten C. The scalar
evaluator walks the existing AST; a register-based VDBE program and compiler
have **not** been implemented by this change.

`SQLSurface.literal` checks the independent `Scalar.admitted` syntax predicate,
evaluates the constant expression, then applies the existing physical value
bounds. This function is used by production INSERT, constant UPDATE assignments,
predicate operands and join operands. `CoreSQL.executeSelectBase` also routes
tableless SELECTs into this layer. The independent token checker now replays
CAST, CASE, boolean literals and parentheses around binary operands.

Declared non-primary column types are now retained in the Core schema and
quoted in canonical `sqlite_schema` SQL. INSERT/REPLACE and constant UPDATE
assignments apply affinity before row admission. Predicates and join literals
apply comparison affinity before the existing index/scan evaluator. Record
decoding restores REAL storage classes, including on independently C-written
files. All file, WAL, lazy-read and CLI SQL entry points now require the concrete
token certificate; BETWEEN replay checks both copies of its desugared operand.
Older Lean-written files whose schema already omitted a declared type retain
that empty type; this change cannot reconstruct declarations lost previously.

Examples for the production `--verified-file` CLI:

```sql
SELECT -7/3, 7%-3, 9223372036854775807+1;
SELECT CAST('123e+5' AS INTEGER), CAST('123e+5' AS NUMERIC);
SELECT CASE WHEN 1 THEN 7 ELSE abs(-9223372036854775808) END;
CREATE TABLE t(id INTEGER PRIMARY KEY,v);
INSERT INTO t VALUES(1,6*7);
UPDATE t SET v=abs(-9) WHERE id=CAST('1x' AS INTEGER);
SELECT v FROM t WHERE id=1+0;
```

## Guarantees and evidence

The existing Core/storage theorem statements remain in place. New registered
theorems cover saturated integer-prefix bounds, exact in-range integer addition,
NULL propagation, zero division, large shifts, wide-product reconstruction,
and constant SELECT state preservation and row-count bounds. Syntax admission
continues to have an independent successful-translation theorem.

These are specific Lean kernel-checked properties, **not** a proof that every
new scalar operation is equivalent to all C SQLite executions. In particular,
algorithm provenance and differential tests do not establish a cross-language
refinement theorem. Standard Lean Float primitives, code generation and the
existing I/O trust boundary still apply. There are no new axioms, external
bindings, or project-local partial definitions.

Run the reproducible differential suite after building:

```sh
lake build
lake exe sqleanite_tests
python3 scripts/run-scalar-differential.py
python3 scripts/run-affinity-differential.py
python3 scripts/run-text-differential.py --seed 353411 --random-cases 500
python3 scripts/run-row-expression-differential.py --seed 353425 --random-cases 500
python3 scripts/run-distinct-differential.py --seed 353431 --random-cases 350
scripts/lean-verification-audit.sh
scripts/live-path-check.sh
```

The differential suite creates two independent databases using the production
Lean CLI and the C SQLite CLI. It checks storage classes, exact binary64 bits,
raw TEXT/BLOB bytes and `PRAGMA integrity_check`. It also exercises reopen,
UPDATE and predicates, SELECT without FROM, error cases, state preservation
on failed INSERTs, and rejected expressions in dead branches. Its seeded
integer and REAL cases are reproducible. Python's SQLite binding only reads
the resulting files; it is not part of the Lean engine.

Before the text and row-expression extensions, validated on Lean 4.35.0: all 160 executable tests, all 924 registered headline
theorems, the verification audit and the live-path audit pass. The new suite
matches **1,120 expressions** exactly and checks six expected evaluation/arity
errors. The 13 existing Core differential cases and 20 reverse-compatibility
cells pass; three reverse cells remain deliberately rejected. The 11 forward
workloads retain their existing result: ten fully clean, and the indexed-shrink
case with its previously declared two allocated-but-unreferenced pages.

The affinity differential suite checks **444 stored values across 12 declared
types and 4,708 SELECTs**, before/after index creation, updates and reopening.
It also checks independently C-created files, a write to a native C image,
four failing writes without mutation, and two explicit mixed-affinity
rejections. Result-set markers distinguish adjacent empty/nonempty query
results; file observations compare storage classes, exact REAL bits and bytes.

The separate 144-probe SQL-surface audit now has **47 matching probes, 97
explicit rejections and no silent differences**. The earlier scalar-port
snapshot had 46 matches, 95 rejections and three differences. Column affinity
now matches; NOCASE and WITHOUT ROWID are rejected. No previously matching
probe regressed. Of the 106 equally weighted feature groups, 26 match all
sampled cases, 12 are partial and 68 are rejected. These samples are not
coverage of the whole SQLite codebase. Local raw logs and reports are in
`../benchmarks/20261024-sqlite-affinity-port/` (outside this Git repository).

## Text/blob scalar extension

Final-checkpoint validation: **6,537 expressions**, with seed `353411` and
500 fresh generated groups, match SQLite 3.53.4 exactly. All 18 invalid-arity
cases reject without mutation. All **161 executable tests**, **929 headline
theorems**, the source audit and the live-path audit pass. The existing
1,120-expression scalar suite and 444-value/4,708-query affinity suite have no
regression. The [machine-readable report](validation/sqlite-text-20261024.json)
records hashes, commands' parameters and separately listed unsupported inputs.
The earlier 2,351-case development run also passed; it is not counted as the
fresh final-checkpoint result.

The functions in `SQLite/Text.lean` run through the same certified production
expression path as arithmetic. They can be used in tableless SELECTs, INSERT
values, constant UPDATE assignments and supported predicate operands. Row-dependent projection support was added by the following extension; general
row-dependent WHERE and UPDATE expressions remain unimplemented.

`substr` counts UTF-8 characters for TEXT and bytes for BLOB. It preserves
SQLite's zero/negative-position and negative-length rules, including Int64
endpoints and the NULL result for a zero-length BLOB. `unhex` permits ignored
characters between complete byte pairs only. `replace` preserves the source
when its pattern is empty even when the replacement is NULL. Scalar `min`
selects the last equal argument and `max` the first, preserving the selected
storage class. Collations remain BINARY. `unicode` reads raw bytes using
SQLite's decoder, including malformed BLOB sequences, without manufacturing
invalid Lean strings.

Kernel-checked properties cover the substring length bound, NULL propagation,
empty-needle search and the empty hex-decoding accumulator. They do not assert
full equivalence of the new functions with C SQLite. The differential suite
compares independently written database files, including exact REAL bits and
TEXT/BLOB bytes, then checks reopening, UPDATE, index predicates and rejection
without mutation. The report records implementation and harness SHA-256 hashes.

Newly allocated text/blob results retain the Core limit of 999,999 bytes.
Surrogate-producing `char` calls and operations requiring invalid UTF-8 TEXT
remain explicit rejections. These are compatibility gaps, not passing cases;
the differential report lists them separately. SQLite's full size limit,
byte-preserving invalid TEXT representation and non-BINARY collations remain
unimplemented.

## Row-dependent SELECT projection

The [fresh final-checkpoint report](validation/sqlite-row-expression-20261024.json)
records **544 queries and 42,581 result rows**, with seed `353421`, no differences
in the admitted expression cases and eight matching errors. All **162 tests**,
**933 headline theorems** and both audits pass. The existing scalar, affinity
and text suites pass again (1,120 expressions; 444 stored values/4,708 queries;
3,037 fresh text expressions respectively). These counts do not include the
known old-path difference or the explicitly rejected DISTINCT ordering case.
The [development negative result](validation/sqlite-row-expression-development-negative-20261024.json)
is retained separately.

`SELECT upper(name), price*2 FROM items` now uses the same scalar evaluator
with explicit column lookup and affinity inputs. Qualified names are checked
against the table or its alias. Name binding and supported-syntax admission
cover the whole expression tree before any row is evaluated, including for
empty tables, LIMIT 0 and dead conditional branches. CASE comparisons preserve
column affinity; unary plus erases affinity as SQLite requires.

The adapter expands stars in place, reads through `Core.execute` and the
existing planner, and converts results through `SQLSurface.value`. Existing
column predicates and source-column ORDER BY work with expression projections.
DISTINCT expression results use SQLite value comparison (including numeric
INTEGER/REAL equality and NULL equality), retain a representative row, and
apply LIMIT after duplicate elimination. DISTINCT ordering is admitted only
when each ordering column is also a directly projected column. Other such
orderings remain explicit rejections: the first development run exposed a
difference when SQLite chose a reverse primary-key scan, and that negative
result is retained in the validation artifacts.

The row adapter has kernel-checked lookup and result-width properties. The
existing Core read, file and durability theorems still build without changing
their statements. No full SQL-semantic refinement theorem for the new scalar
projection adapter is claimed. The differential report labels its measurements
as query-output comparisons, distinct from the exact storage-bit comparisons
in the scalar INSERT suites.

The preceding row-expression checkpoint reproduced a direct-column DISTINCT
bug: values `(1,1,2)` with `SELECT DISTINCT v FROM d ORDER BY id LIMIT 2`
returned only `1`. The subsequent Core correction now retains first
representatives and applies LIMIT after duplicate elimination, returning
`1,2`. The bag denotation models that ordered prefix explicitly; the existing
read and permutation theorem statements are preserved and rechecked. The old
negative result remains in the earlier checkpoint report.

At the DISTINCT/LIMIT checkpoint, direct-column queries still used
representation equality: `1` and `1.0` could survive as separate rows. That
negative result is preserved in its report. The numeric DISTINCT checkpoint
below corrects this discrepancy with a shared exact comparison key. It does
not claim to resolve all ordering, grouping or set-operation semantics.

The fresh tests also exposed and fixed two CLI issues: empty/NULL-only rows
must emit an empty line, and rendered TEXT stops at its first NUL. File, WAL
and timed CLI modes share those fixes. A later malformed UTF-8 probe found a
missing signed-Int32 conversion in `unicode`; the exact failing bytes are now
a fixed regression. These negative checkpoint results are retained rather
than counted among passing cases.

## Final DISTINCT/LIMIT and CLI checkpoint

The [final checkpoint report](validation/sqlite-distinct-cli-20261024.json)
records **604 queries / 42,873 result rows** at fresh seed `353424`, and
**6,539 text/blob expressions** at fresh seed `353415`, with no differences in
those admitted cases. The 1,120-expression scalar suite and the 444-value /
4,708-query affinity suite also pass. All **163 executable tests**, **938
registered headline theorems**, the source audit and the complete live-path
audit pass. The report hashes all library sources and `Main.lean`.

The direct-column LIMIT reproduction now returns `1,2` in both engines, and
60 generated indexed/range/ordered/empty DISTINCT queries provide regression
coverage. Empty rows and NUL text rendering match in all three CLI modes.
The [first fresh negative checkpoint](validation/sqlite-distinct-cli-development-negative-20261024.json)
and [Unicode signed-result failure](validation/sqlite-unicode-development-negative-20261024.json)
remain available. That historical report separately records the then-unresolved
INTEGER/REAL DISTINCT difference; it was not counted as a passing case.

## Numeric DISTINCT checkpoint

The [fresh final-checkpoint report](validation/sqlite-numeric-distinct-20261024.json)
records **10,220 numeric DISTINCT queries** with no differences at seed
`353431`: 350 newly generated pairs plus 15 fixed boundary pairs, exercised
before and after index creation and reopening. Both direct-column and
expression projections retain the first original representative; INTEGER/REAL
equality, signed zeros, signed-64 endpoints, neighboring values around `2^53`,
subnormals, infinity, NULL and numeric TEXT separation are covered. Multi-column
permutations and post-DISTINCT LIMIT are included. BLOB/TEXT separation is
checked as typed Core values in the executable tests; this particular query
suite does not claim to compare arbitrary BLOB shell output or exact binary64
SELECT result bits.

`Core.distinctValueKey` in `CoreDistinct.lean` uses binary64's exact significand and exponent
to identify integral REALs that fit signed 64-bit INTEGER. It leaves all other
representations unchanged and never converts an INTEGER to an inexact Float.
The keys are only used for comparison; output and stored values are untouched.
Both production projection paths use the same first-representative algorithm.

The existing read and column-permutation theorem statements still compile.
The independent bag denotation now selects the first original representative
of each key from the projected bag, then applies the ordered LIMIT. New
kernel-checked statements cover source membership, key uniqueness, retained
representatives, key-preserving maps and column permutation. These properties
are not a complete proof of equivalence between the key normalizer and every
SQLite collation or runtime value.

All **164 executable tests**, **945 registered headline theorems**, the source
audit and the live-path audit pass. Fresh regression checks also pass: 604
row-expression queries / 42,873 result rows at seed `353425`, 6,539 text/blob
cases at seed `353416`, 1,120 scalar expressions, and 444 affinity values /
4,708 queries. Source, executable and numeric-harness hashes are in the report.
The earlier numeric DISTINCT failure now has a required passing regression.

The [remaining-gap probes](validation/sqlite-remaining-gaps-20261024.json) are
reported separately: seven explicit feature rejections and five successful
queries with wrong output. In particular, `UNION`, `INTERSECT`, `EXCEPT` and
`GROUP BY` still use representation equality in their older paths, and
`SELECT DISTINCT v ... ORDER BY b` can choose the wrong order when `b` is not
projected. These are known defects, not passing or silently excluded cases.

## SQL compound set-operation checkpoint

The [final checkpoint](validation/sqlite-compound-20261024.json) records
**680 compound queries / 3,305 result rows**, with 600 fresh random cases at
seed `353441`, matching SQLite 3.53.4. It covers mixed left-associative operator
chains, empty arms, NULL, INTEGER/REAL equality, text separation, exact numeric
boundaries, multiple result columns and persisted table inputs. Three expected
error cases reject without changing the file. All **165 tests**, **950
registered headline theorems**, and both audits pass. The existing row,
DISTINCT, scalar, text and affinity regressions also pass; their separate
metrics and source hashes are retained in the report.

`CoreCompound` gives UNION, INTERSECT and EXCEPT an explicit comparison-key
semantics and preserves UNION ALL multiplicities. Outputs retain original
storage classes and use SQLite's ascending BINARY compound order. The pinned
SQLite merge chooses the right UNION arm on equal keys, retaining the first
matching row within that arm; INTERSECT and EXCEPT retain the left arm's first
representative. An earlier last-representative implementation failed 24
persisted-table queries; the [negative result](validation/sqlite-compound-development-negative-20261024.json)
is retained and those cases now pass.

SQL membership and multiplicity theorem statements now explicitly refer to
comparison keys. This corrects the old raw-representation contract rather than
claiming that its equality domain was already SQLite-equivalent. The production
SQL-text binary and recursive compound proofs reach the new independent
key-bag denotation, retain exact output-row equality, and preserve read-only
state. The older optimizer's representation-equality algebra remains labelled
as such. Source membership, row widths and key uniqueness remain proved.

The three previously recorded numeric UNION/INTERSECT/EXCEPT examples are now
fixed. GROUP BY numeric equality, nonprojected DISTINCT ordering, compound
ORDER BY/LIMIT and the larger feature gaps listed below remain outstanding at
this checkpoint. Passing these cases does not establish 100% compatibility.

## Numeric GROUP BY and aggregate representatives checkpoint

The [fresh final checkpoint](validation/sqlite-group-20261024.json) records
**596 queries / 20,130 result rows**, including 500 fresh generated cases at
seed `353451`, matching SQLite 3.53.4. Three binding/overflow errors reject
without file mutation. All **166 tests**, **955 registered headline theorems**,
the verification audit and the live-path audit pass. Compound, row-expression,
DISTINCT, text, scalar and affinity regressions pass separately; counts and
source/executable/harness hashes are retained in the report.

GROUP BY now uses the same numeric comparison keys as DISTINCT, retaining
original values for output. Groups use lexicographic SQLite BINARY order.
MIN/MAX retain the first non-NULL equal extreme, including its storage class.
Group-column output follows the source row selected by the last distinct
MIN/MAX accumulator; identical aggregate expressions share that accumulator.
Without MIN/MAX, group-column output uses the first source row. All-NULL
extrema select the last source row, matching the pinned accumulator behavior.

The new registered proofs show that representatives belong to the input group
and preserve its comparison key. The materialized count refinement now states
bag equality, because Core group presentation is sorted; the independent
aggregate denotation records the chosen original key. This is not a formal
cross-language proof of every SQLite aggregate. REAL SUM, arbitrary aggregate
expressions, collations, grouped ORDER BY/LIMIT and planner-dependent output
outside this tested shape remain open. The earlier numeric GROUP BY mismatch
is fixed; its historical negative report remains unchanged.

## Row-expression WHERE checkpoint

The [fresh final checkpoint](validation/sqlite-predicate-20261024.json) records
**1,216 ordered queries / 21,392 result rows**, using seed `353461` with 500
fresh generated expressions, each run without indexes and after index creation.
All compared rows agree with SQLite 3.53.4; thirteen binding/overflow errors
also agree without file mutation. All **167 executable tests**, **958 registered
headline theorems**, and both audits pass. The separate affinity regression now
checks 4,709 queries: its formerly rejected TEXT-versus-numeric-CAST predicate
matches. Mixed-affinity joins remain rejected. All earlier SQL suites pass.

Single-table projection queries now evaluate arithmetic, scalar functions,
column-to-column comparisons, column affinity and three-valued conditions in
WHERE. Core.execute supplies the input rows. A bounded scan filters, projects,
removes duplicate outputs and stops at LIMIT when source order already matches;
other source-column ordering sorts the surviving output. Binding checks run
before empty-input or LIMIT-zero shortcuts. The shared WHERE branch evaluator
also serves tableless SELECT. Top-level AND constraints are split before branch
evaluation; constant constraints execute before the table scan. The earlier
error-suppression mismatch is retained in the [development negative report](validation/sqlite-predicate-development-negative-20261024.json)
and is now a required passing regression.

Registered contracts cover scan length, no evaluation at LIMIT zero, and
read-only state. Existing successful Core predicate translation proofs still
compile; expression fallback does not replace them with a claim of full SQL
refinement. Aggregate, join, UPDATE and DELETE row predicates remain outside
this new route. Two **known planner-dependent diagnostics** are retained in the
report: without ORDER BY, a covering-index scan can reach a failing expression
before LIMIT while the current Core table scan does not. Those cases are not
included in the passing count. General planner-dependent error/evaluation order
is still a compatibility gap.

The full reverse-file matrix accepts **53 cells** and explicitly rejects three
unsupported schema shapes. The 13 Core differential cases pass. Of 11 forward
file workloads, ten pass SQLite integrity_check; the indexed-shrink workload
still has its pre-existing bounded orphan-page exception. These are separately
reported file results, not proof of complete database or WAL compatibility.

## Indexed-shrink file-integrity checkpoint

The [fresh checkpoint](validation/sqlite-index-reclaim-20261024.json) checks
**264 persisted images** from 12 fresh seeded fixtures (`353471`), five
shrink/refill cycles each, through both rollback-journal and WAL writers.
SQLite 3.53.4 independently reads every image: integrity_check is always `ok`,
and schema, typed values, index lookup and the untouched neighbouring table
agree with independently SQLite-written files. All **168 tests**, **959
registered headline theorems**, the verification audit and live-path audit pass.
All eleven forward workloads are now clean with **zero orphan exceptions**.
The full reverse matrix retains 53 accepted cells and three explicit rejections;
13 Core differential cases and the SQL regressions in the report pass.

The historical 200-row indexed-delete exception was a real allocation bug:
the index root was page 8, while its children were pages 6 and 7. Rewriting the
root-to-end interval left both children orphaned. The [negative checkpoint](validation/sqlite-index-reclaim-negative-20261024.json)
preserves that layout. Local tail replacement now verifies the old canonical
index bytes over the entire physical interval. Layouts that fail this check
use the existing proved, freelist-aware full commit. The new registered theorem
exposes the guard's exact byte-image and interval-length equations; it does not
claim a proof of all foreign index layouts or the real filesystem.

The strict page-reclamation regression also passes five 200-row and seven
1,000-row empty/refill cycles. Every phase must be clean. The previous bounded
orphan allowance has been removed from both executable checks and generated
compatibility documentation. The extra old-index encoding/check can increase
fallback write cost; correctness takes priority here. Full WAL locking/recovery,
other writer page sizes and unsupported schema shapes remain open.

## Row-dependent UPDATE checkpoint

The [fresh final checkpoint](validation/sqlite-update-20261024.json) records
**520 successful UPDATE statements**, seed `353481`, with 250 fresh generated
updates in each of the rollback-journal and WAL modes. After every statement,
an independent SQLite reader checks 122 rows across INTEGER-primary-key and
hidden-rowid/TEXT-primary-key tables: storage classes, exact binary64 bits and
TEXT/BLOB bytes match. Sixteen expected failures leave the database/WAL bytes
unchanged; transaction rollback also preserves the original state. Every image
passes integrity_check. All **169 executable tests**, **961 registered headline
theorems**, both audits, all eleven forward file workloads, and the separately
reported affinity/predicate/reclamation regressions pass.

UPDATE now binds row-dependent RHS and WHERE expressions, computes every RHS
against the original row, and applies destination-column affinity afterwards.
This includes column swaps and the last assignment to a repeated destination.
The production fallback prepares a bounded trace of Core point updates and
publishes only after the complete trace succeeds. Registered contracts expose
the exact executed trace and its row-count bound; existing constant-UPDATE
translation theorems remain intact. These properties are not a full SQLite
UPDATE refinement proof. Primary-key writes, non-ABORT conflict policies,
UPDATE FROM/RETURNING, all constraint forms and full planner evaluation-order
parity remain open. Unsupported functions remain rejected during admission,
including some overwritten assignments SQLite can ignore on unindexed tables.
The [development negative](validation/sqlite-update-development-negative-20261024.json)
records why skipping their validation wholesale was incorrect for indexed UPDATE.

The stored-value test closes each observer explicitly. An initial Python test
used a connection context manager without closing the connection, exposing a
separate, real cross-engine WAL limitation. A [reproducible negative probe](validation/sqlite-wal-open-reader-negative-20261024.json)
now holds a **SQLite 3.53.4** connection open while SQLeanite replaces the WAL.
Another SQLite 3.53.4 reader then reports `file is not a database`; after the
held connection closes, the same WAL reads correctly and passes integrity_check.
The old shared-memory wal-index still refers to old frame offsets. SQLeanite's
whole-WAL rename does not implement SQLite's SHM coordination. This issue is
**unresolved**, excluded from the passing sequential file-interchange count,
and prevents a claim of complete cross-engine WAL compatibility.

## Current gap inventory

The [current diagnostic inventory](validation/sqlite-current-gaps-20261024.json)
rechecks retained counterexamples and additional feature probes. It contains
six matches, nineteen explicit rejections and one wrong-result case. These
counts are a selected diagnostic set, **not a compatibility percentage**. The
remaining wrong result is DISTINCT ordered by a nonprojected column. CTEs,
subqueries, views, triggers, implicit-rowid schemas, general aggregates,
row-expression DELETE, window functions, OFFSET, IN, UNIQUE indexes and other
features still fail the current production surface. The separate open-reader
WAL negative above remains unresolved as well. The accepted 100% target has
not been reached.

## Still missing

This step does not implement general aggregate/join/DELETE WHERE expressions,
the complete VDBE, the full planner, all DDL/constraints, views/triggers,
subqueries/CTEs/windows, the rest of the scalar/aggregate functions, JSON,
virtual tables/extensions, all collations/encodings, or the full SQLite WAL
and locking protocol. Tableless ORDER BY and aggregates are still rejected.
This is the default 17-digit REAL formatting path, not general SQLite printf
or per-connection floating-point precision configuration.

Stored column affinity is implemented for the admitted Core SQL subset.
Single-table scalar predicates can convert both operands as required by their
affinities. Mixed-affinity joins (for example TEXT/NUMERIC joins) remain
explicit rejections. Admitted
rows carry a canonical-affinity invariant: malformed foreign records which
violate it are rejected. Schema round-trip and read normalization proofs retain
the existing codec contracts; comparison fixed-point proofs justify keeping
the existing ordinary index key representation. These are not a full C-to-Lean
semantic equivalence proof.

Non-BINARY column collations and WITHOUT ROWID are now rejected before schema
creation, instead of being silently discarded. Those features are still unported.
Invalid UTF-8 BLOB-to-TEXT conversion is explicitly rejected rather than
replacing bytes. Collations and column references in constant expressions are
rejected, including in dead branches. Do not infer a percentage of SQLite
coverage from the number of ported functions or passing test expressions.

### DISTINCT source ordering checkpoint (2026-10-24)

The production single-table path now retains the first duplicate representative
before sorting by an unprojected source column. A primary-key order controls
scan direction; an unrelated source order sorts the surviving representatives.
Both direct-column and scalar-expression projections use this rule. The
persisted-query recognizer yields to the same executor for these shapes.
`TranslatedRead.query` now states the direct-route premise explicitly instead
of claiming that every translated ordering still uses the old Core query.

Frozen implementation SHA-256:
`3bee0cf61ae7ebc278a927ef9345f5fa72ad52f209a8710d95a899bb0da72cfc`.
Fresh seed 353491 checked **8,400 queries** across both file modes, with and
without an index, including ascending/descending primary keys, arbitrary
source-column orders, scalar projections, DISTINCT and LIMIT. All outputs
matched pinned SQLite 3.53.4 and reads preserved the database/WAL bytes.
Seed 353492 checked **305 row-expression queries / 18,879 output rows**, with
8 matching errors. The former DISTINCT-expression ordering rejection is now
a positive regression. Reports are in
`docs/validation/sqlite-distinct-source-order-20261024.json` and
`docs/validation/sqlite-row-expression-source-order-20261024.json`.
All **170 executable tests**, **961 registered headline theorems**, the full
build and both audits passed. This closes the retained DISTINCT source-order
counterexample; it is not a whole-SQLite compatibility result. Covering-index
scan choices and general ORDER BY expressions remain separate work.

### Atomic scalar-predicate DELETE checkpoint (2026-10-24)

DELETE now accepts the same bound row expressions as scalar WHERE and UPDATE,
including table aliases, functions, arithmetic, CASE and SQL three-valued
truth. Selected rowids become a bounded Core command trace. The predicate scan
finishes before mutation starts, so a later expression error preserves the
whole statement's file state. RETURNING, triggers and foreign-key actions
remain outside this implementation.

The new suite exposed a parse-time binding difference: SQLite folds
`missing+1 AND 0` to zero before name binding, but preserves function calls
under AND so that their errors remain observable. The common scalar layer now
implements that explicit AST normalization (including CAST's operator status),
then performs normal binding and evaluation. This is separate from the later
WHERE branch simplifier. Subquery syntax remains conservatively excluded from
this fold until that syntax is implemented.

Frozen implementation SHA-256:
`ada0e598e845cf98c0ec009d00cd6d02ddc2041c3d78391aae90c22f487b7c26`.
Fresh seed 353502 checked **382 DELETE statements**, **14 matching errors**,
independently decoded retained values, integrity after every successful delete,
byte preservation after errors, and rollback in both production file modes.
Seed 353503 checked **816 predicate queries / 13,222 output rows** without a
difference. Full build, **171 executable tests**, **963 registered headline
theorems** and both audits passed. Reports:
`docs/validation/sqlite-row-delete-20261024.json` and
`docs/validation/sqlite-predicate-delete-regression-20261024.json`.
The point-delete trace can cost more than a single bulk predicate deletion;
this checkpoint does not claim planner or performance equivalence.

### SQLite-created WAL recovery checkpoint (2026-10-24)

The production WAL reader now decodes SQLite-created logs with either checksum
byte order and all eight page sizes from 512 through 65536. It stops at the
first incomplete, salt-mismatched, zero-page-number or checksum-invalid frame,
replays only the last committed prefix, and obtains unchanged pages from the
main database. Empty logs and invalid headers fall back to the main file; a
checksum-valid unsupported WAL version is rejected. Repeated pages use the
newest committed frame and the commit's database size bounds visibility.
The page decoder uses the recovered header's geometry. All SQL/WAL parsing,
checksum and replay logic remains Lean; no host binding was added.

Unlike the older reverse-matrix WAL case, these fixtures are copied while a
pinned SQLite connection is open, before its close-time checkpoint. Thus the
WAL really contains partial-page transactions, with untouched overflow pages
remaining in the main file. The previous reader failed **30 of 32** such
4096-byte development cases; that negative evidence is retained in
`docs/validation/sqlite-wal-recovery-negative-20261024.json`.

Frozen implementation SHA-256:
`09da9aa884ca4a1560c9e146e0d38b09fe3aca8caee7fb37b4e763beccabe674`.
Fresh seed 353512 checked **768 cases**, including **48 matching version
errors**, with no discrepancy against SQLite 3.53.4. Every read preserved the
main/WAL bytes. The report is
`docs/validation/sqlite-wal-recovery-20261024.json`.
A fresh 220-UPDATE regression across both file modes, including 16 matching
errors and transaction rollback, also passed. The full build, **172 executable
tests**, **967 registered headline theorems**, both audits and the 53 accepted
reverse-matrix cases passed (3 other matrix shapes remain unsupported).

The new registered contracts prove invalid-frame stopping, invisible
uncommitted tails, main-page fallback and newest-frame selection. They are
component contracts, not a proof of all SQLite WAL semantics. Writer output
still uses 4096-byte complete images; live cross-engine writers/readers still
need SQLite-compatible locking and wal-index coordination. That separate
open-reader counterexample remains unresolved. The format/recovery reference
is SQLite's [WAL file format](https://www.sqlite.org/fileformat2.html#walformat)
and the pinned source's `walIndexRecover`/`walDecodeFrame` routines.

### Scalar IN/NOT IN and indexed search checkpoint (2026-10-24)

Scalar IN and NOT IN now implement empty-list folding, SQL NULL truth, numeric
comparison, and left-operand affinity without importing RHS column affinity.
A singleton constant list normalizes to equality with unary plus on its RHS.
Short or row-dependent lists use a short-circuit comparison chain; longer
constant lists evaluate all RHS expressions before the LHS. Empty lists retain
function binding while suppressing evaluation, following SQLite's parser rule.

Expression scans also recognize primary-key equality and constant primary-key
IN searches, plus a sole indexed IN constraint. Search keys are evaluated before
the row scan; a stronger primary equality bounds the rows first. Columns fixed
by that equality participate in WHERE's constant-IN classification. Entire
WHERE terms made constant by that binding run before the lookup, including on
empty tables. The normal projection and assignment evaluator keeps its original
row and affinity information. These explicit rules do not implement SQLite's
complete cost-based planner or every combination of competing constraints.

Two development counterexamples changed the implementation: eager IN search
keys were initially missed at LIMIT 1/empty tables, then fixed-column constant
terms were initially evaluated too late on an empty table. Both reports remain
in `docs/validation/sqlite-in-list-development-negative-20261024.json` and
`docs/validation/sqlite-in-fixed-column-negative-20261024.json`.

Frozen implementation SHA-256:
`12306ff67f34848324db7a479cd5c77b592da2967bcdbbff64080eddaf4d4e34`.
Fresh seed 353524 checked **773 SELECTs / 22,293 output rows**, including
**26 matching rejections**, with no discrepancy. Seeds 353525 and 353526
checked **186 UPDATEs** and **188 DELETEs** across both file modes, including
IN predicates, 18/16 matching errors respectively, image integrity, failed
statement byte preservation and rollback. Full build, **173 executable tests**,
**968 registered headline theorems** and both audits passed. Reports are
`docs/validation/sqlite-in-list-20261024.json`,
`docs/validation/sqlite-in-list-update-20261024.json`, and
`docs/validation/sqlite-in-list-delete-20261024.json`.
Subquery IN, custom collations and complete planner/evaluation-order parity
remain separate work; these results are not a compatibility percentage.


### Single-table LIMIT/OFFSET checkpoint (2026-10-24)

Single-table row scans now implement OFFSET after filtering and duplicate
removal, including the comma spelling, negative limits, negative offsets and
explicit OFFSET zero. When the source already supplies the requested order,
skipped ordinary rows do not evaluate their projection; DISTINCT still
computes the candidate key before skipping a unique output. Other source-column
orders sort the representatives before slicing. Names remain bound on empty
input and LIMIT zero. LIMIT zero skips literal OFFSET conversion, including
NULL and out-of-range numeric literals, and normalizes the unused offset to zero.

The independent grammar checks signed 64-bit literal limits and offsets against
the translated query fields. General LIMIT expressions, aggregate/join slicing
and arbitrary ORDER BY expressions remain outstanding. The original failed
suite and the later zero-limit normalization counterexample are retained in
`docs/validation/sqlite-limit-offset-negative-20261024.json` and
`docs/validation/sqlite-limit-offset-zero-development-negative-20261024.json`.

Frozen implementation SHA-256:
`07fdaa27f110076d842d6f1427e85b469a427c9f5beada5f46c2600f6237b664`.
Fresh seed 353536 checked **950 queries / 6,878 output rows** across both file
modes, including **18 matching errors**, with no differences and unchanged
main/WAL bytes. Seed 353537 checked **716 predicate queries / 12,938 output
rows**, including indexed scans, plus **13 matching errors**. Reports are
`docs/validation/sqlite-limit-offset-20261024.json` and
`docs/validation/sqlite-predicate-limit-offset-20261024.json`.
The full build, **174 executable tests**, **970 registered headline theorems**
and both audits passed. New component contracts cover zero-offset equivalence
and no scan evaluation for LIMIT zero. The retained gap inventory still has
16 explicit rejections; this suite is not a whole-SQLite coverage percentage.


### Numeric SUM, AVG and TOTAL checkpoint (2026-10-24)

`SQLite/AggregateSum.lean` ports the pinned `func.c` ordered accumulator:
exact signed-integer accumulation, conversion to compensated binary64 sums,
wide-integer splitting, delayed integer-overflow errors, and their cancellation
by a later non-integer input. Numeric TEXT conversion preserves decimal/exponent
spelling; other TEXT/BLOB values use SQLite's numeric-prefix conversion. NULLs
do not contribute. AVG and TOTAL always produce REAL when non-NULL; empty SUM
and AVG are NULL, empty TOTAL is 0.0. Infinite/NaN compensation and final NaN
follow the SQLite result rules. The original all-integer Core SUM fast path and
its mathematical-sum claims remain intact. Grouped AVG/TOTAL and single-column
AVG/TOTAL now use the same physical-value accumulator.

The group refinement contract preserves the exact integer statement when
integer extraction succeeds and explicitly describes the ordered accumulator
otherwise. Four new contracts concern NULL steps and all-NULL inputs; they do
not establish general floating-point equivalence to compiled SQLite. The source
reference is pinned `func.c` (`sumStep`, `sumFinalize`, `avgFinalize`,
`totalFinalize`) and the [aggregate documentation](https://www.sqlite.org/lang_aggfunc.html).
General aggregate expressions, aggregate row-expression WHERE, aggregate
DISTINCT, and grouped ordering/slicing remain separate work at this checkpoint.

The first differential run found a TEXT-with-NUL type difference and a separate
CLI rendering difference. Numeric TEXT ending at a NUL now uses the same
integer recovery rule; production list-mode output now writes raw TEXT/BLOB
bytes up to the first NUL, including invalid UTF-8, instead of silently changing
them to empty text or hex notation. This does not change stored values.
The six development failures are retained in
`docs/validation/sqlite-numeric-aggregate-development-negative-20261024.json`.

Frozen implementation SHA-256:
`c95edd636c514a7bf888b7a242ae3ecfe87d234e26af31ea441b592ebbaee4ed`.
Fresh seed 353543 checked **1,772 queries / 6,896 result rows**, including
**16 matching errors**, across both production file modes and 249 input groups.
There were no differences, and reads preserved main/WAL bytes. The suite includes
raw row output and mixed grouped extrema, so its count is not exclusively
aggregate arithmetic. Seed 353544 checked **346 grouped queries** plus
**3 matching errors** without a regression. The existing scalar value/binary
storage suite also passed. Full build, **175 executable tests**, **974 registered
headline theorems** and both audits passed. Reports are
`docs/validation/sqlite-numeric-aggregate-20261024.json`,
`docs/validation/sqlite-group-numeric-aggregate-20261024.json`, and
`docs/validation/sqlite-scalar-numeric-aggregate-20261024.json`.
The diagnostic inventory still contains 14 explicit SQL rejections and is not
a whole-SQLite compatibility percentage.


### Bound aggregate arguments and DISTINCT checkpoint (2026-10-24)

`CoreAggregate` now evaluates ordinary single-table COUNT/SUM/AVG/TOTAL/MIN/MAX
terms with bound scalar arguments, multiple aggregate result columns, and
DISTINCT input elimination using the exact Core BINARY numeric keys. The query
first filters Core source rows with the shared expression-WHERE evaluator,
including constant-term preparation and supported indexed searches. LIMIT zero
skips evaluation after binding; OFFSET skips the finalized aggregate output,
so it does not suppress errors encountered while accumulating inputs.

COUNT() shares COUNT(*)'s row count, including empty inputs. This SQLite case
was the 12-failure development counterexample retained in
`docs/validation/sqlite-aggregate-expression-development-negative-20261024.json`.
Qualified column arguments go through binding before the older direct-column
optimization, so a wrong table name/alias fails even on empty input or LIMIT
zero. Scalar MIN/MAX with multiple arguments keeps its scalar classification.

Frozen implementation SHA-256:
`900a7e22179f518b009c616320f87f9369bfdc1cbad37a2c7a35e4353a9fc1f8`.
Fresh seed 353551 checked **1,086 queries**, including **126 matching errors**,
across both production file modes, with no output or rejection-status mismatch.
Seed 353552 checked **992 numeric-aggregate/regression queries**, including
**16 matching errors**. All reads preserved main/WAL bytes. Reports are
`docs/validation/sqlite-aggregate-expression-20261024.json` and
`docs/validation/sqlite-aggregate-expression-numeric-regression-20261024.json`.
Full build, **176 executable tests**, **977 registered headline theorems** and
both audits passed. The new registered contracts cover the COUNT(*) Core count,
filtered-row length and unchanged Core state. These are component contracts;
the CLI comparisons do not assert identical diagnostic wording or query plans.

The new term evaluator does not yet cover aggregate expressions nested in
result expressions, mixed bare/aggregate columns, source-free aggregates,
GROUP BY expression terms, HAVING or aggregate ORDER BY. The previous direct
column GROUP BY route remains available. The diagnostic inventory now retains
12 explicit rejections; it is not a whole-SQLite coverage percentage.


### Implicit rowid tables and foreign page-size writes (2026-10-24)

Tables without an explicit PRIMARY KEY now use a hidden rowid while keeping
that internal field out of the SQL schema and star projections. A no-declared-key
sentinel round-trips through the proved canonical schema printer/parser. The
internal declared-key cache uses the rowid for such rows, avoiding a false
uniqueness collision on NULL. Explicit rowid/oid/_rowid_ names resolve after real
column names, so shadowing remains visible. INSERT validates column names and
supports DEFAULT VALUES, omitted/NULL INTEGER PRIMARY KEY allocation, explicit
rowids and negative maxima. Automatic allocation uses max(rowid)+1, or 1 for an
empty table. The localized append path now explicitly checks the automatic
allocation premise before applying its after-all-rows proof.

The new persisted-image test exposed seven existing rollback-mode write
rejections for non-4096 files, retained in
`docs/validation/sqlite-implicit-rowid-page-write-negative-20261024.json`.
The production engine now handles that case with a separate full-image
publication path. It encodes and verifies a canonical 4096-byte image before
renaming a synced temporary file over the original and syncing the directory.
This is page-size normalization, not preservation of the source geometry.
The old same-geometry journal path stays separate. Multiply linked files are
explicitly rejected by the conversion path; live cross-engine coordination and
preserving other requested page sizes remain unfinished.

The existing OS rename binding now preserves destination ownership and access
bits and syncs that metadata before publication. No binding or SQLite C code
was added. Its source SHA-256 is
`cb7b0d02bd86a1c4b42621f78f94cbefb73bcf52574ce4287e985c7eddb2fa3c`.
The separate `AtomicFileReplacement` model proves complete old/new images at
modeled crash prefixes and the completed new image. Host rename/sync behavior
remains a stated trust assumption. Injected temporary-sync failures and corrupt
staging bytes preserved the original image; a directory-sync failure after
rename left the complete new image. SQLite checked each image and all retries
succeeded. These are I/O-failure tests, not physical power-loss experiments.

Frozen Lean/Main implementation SHA-256:
`f4640a1b69605aa1ef0fc03454999b64ef9962b38513df1084d65adceb1f4dcd`.
Fresh seed 353561 checked **1,854 statement outcomes**, including **126 matching
errors**, across **18 file variants**, with no discrepancy. Each step checked
SQL output, independent SQLite reads and integrity, unchanged main/WAL bytes on
errors, and owner/group/access bits. Seed 353562 checked **686 aggregate
regressions**, including **126 matching errors**, without a difference. Full
build, **178 executable tests**, **981 registered headline theorems**, both
audits and **57 accepted reverse-matrix cells** passed; 2 reverse shapes remain
declared unsupported. Reports are
`docs/validation/sqlite-implicit-rowid-20261024.json`,
`docs/validation/sqlite-implicit-rowid-aggregate-regression-20261024.json`, and
`docs/validation/sqlite-page-conversion-host-checkpoint-20261024.json`.
Allocation after the maximum signed rowid, AUTOINCREMENT, rowid updates, nullable
non-integer primary keys and general constraints remain separate SQL work.
The selected diagnostic inventory still has 11 explicit rejections.


### Rowid and INTEGER PRIMARY KEY UPDATE (2026-10-24)

UPDATE now binds rowid aliases and INTEGER PRIMARY KEY targets, evaluates all
right-hand sides against the original rows, and applies each row change as a
Core deletion/insertion pair. The entire command trace must succeed before a
new state can be published. A completed row is validated before the pair, so
NULL and non-integral rowids cannot invoke INSERT's automatic allocation.
Duplicate assignment targets retain the last expression while binding every
expression. Reported changes count logical rows, not the two Core commands.
The batch carries a proof of its paired command count; registered theorems
bound selected-row changes and connect the SQL path to the Core trace. These
are component facts, not a SQLite equivalence proof.

At frozen Lean/Main SHA-256
`820f0dc89c2378136838161f2ba0300f35aee304ac7bb7ed477cd7c88e05c041`,
fresh seed 353571 passed **1,472 independent UPDATE outcomes**, including
**549 matching errors**. Eight phases cover explicit/implicit rowids,
indexed/unindexed tables and both file modes. Each checks resulting rows,
SQLite reads and integrity of an independent image, and unchanged main/WAL
bytes after errors. Negative rowids, INTEGER limits, original-row binding,
duplicate assignments, aliases, collisions and transaction rollback are included.
Seed 353572 also passed **186 ordinary UPDATE regressions**, **18 expected
errors**, and rollback in both modes. Reports are
`docs/validation/sqlite-rowid-update-20261024.json` and
`docs/validation/sqlite-rowid-update-regression-20261024.json`.

Full build, **179 executable tests**, **983 registered headline theorems**, both
audits and the full reverse matrix (**57 accepted, 2 declared unsupported**)
passed. The selected gap inventory now has **10 explicit rejections**,
**17 matches** and **1 both-reject** case; it is not a coverage percentage.
Declared non-rowid primary-key changes, conflict policies beyond ABORT,
triggers and foreign-key actions still need separate implementations.


### ROUND fixed-decimal semantics (2026-10-24)

The live scalar evaluator now implements one- and two-argument `round()`.
It follows pinned `func.c:roundFunc`: NULL propagation after eager argument
evaluation, saturated integer precision clamped to 0..30, the integral
half-away-from-zero path, and the no-fractional-bits large-magnitude path.
Other values use the pure `%!.*f` decimal decoder followed by the existing
SQLite decimal parser. This retains the 17-significant-digit shortening rule
when fixed decimal precision selects that branch. No host binding was added.
The precision bound and left/right NULL laws are registered component proofs;
complete rounding equivalence remains differential evidence.

Frozen Lean/Main SHA-256:
`09ae145f6a0778aeb244db32c7f41164d41dc9659be10e8e5683ee9f17a42029`.
Fresh seed 353581 passed **7,216 stored result comparisons** over both file
modes, checking storage classes and exact binary64 bits with independent
SQLite image readers and integrity checks. Inputs include random finite bit
patterns, decimal midpoint neighbours, subnormals, infinities, numeric TEXT
and BLOB prefixes, NULL, negative and oversized precision. **26 query outcomes**,
including **12 matching errors**, additionally check row expressions, output,
aggregate use and lazy/dead evaluation. The existing **1,120-case scalar
regression** and its error/persistence checks also passed. Reports:
`docs/validation/sqlite-round-20261024.json` and
`docs/validation/sqlite-round-scalar-regression-20261024.json`.
Full build, **180 executable tests**, **986 registered headline theorems** and
both required audits passed. The selected diagnostic inventory has 9 explicit
rejections, 18 matches and 1 both-reject case; this is not a compatibility rate.


### LIKE, GLOB and ESCAPE (2026-10-24)

The production scalar path now supports LIKE/GLOB operators and functions,
NOT LIKE/NOT GLOB and the LIKE ESCAPE clause. The independent token grammar
checks each infix operand and escape expression. A pure suffix matcher handles
wildcards, ASCII-only LIKE case folding, GLOB classes/inversion/ranges, malformed
classes and escaped wildcard characters. Its byte decoder follows SQLite's
permissive UTF-8 rules for BLOB inputs, including isolated continuation bytes,
overlong sequences, surrogate replacements and NUL termination. SQL TEXT still
uses the existing UTF-8 representation; this does not claim full invalid-TEXT
support elsewhere. Pattern bytes are limited to the pinned default 50,000;
length, ESCAPE and NULL checks follow the original evaluation order.

Frozen Lean/Main SHA-256:
`ed6782eb87e7f3a381418ebd94fae5f32022d1ca350f48e646031118196ade6a`.
Fresh seed 353591 passed **14,126 stored-value comparisons** across both file
modes and **40 query outcomes**, including **24 matching errors**. Separate
SQLite image readers verified values and integrity before and after predicate
mutations. Tests cover functions/infix syntax, Unicode, arbitrary BLOB bytes,
ESCAPE including wildcard escapes, malformed classes, indexed WHERE scans,
UPDATE/DELETE and the pattern-size boundary. Failed statements preserve the
main/WAL bytes. The fresh text/blob regression (seed 353592) passed **2,739
cases** and **18 matching errors**; its explicit pre-existing rejections remain
listed in the report. Reports are
`docs/validation/sqlite-pattern-20261024.json` and
`docs/validation/sqlite-pattern-text-regression-20261024.json`.

Full build, **181 executable tests**, **989 registered headline theorems** and
both audits passed. Registered component facts cover non-ASCII case preservation,
the empty-pattern boundary and bounded-pattern NULL input. They do not prove
full equivalence with SQLite's C matcher. The selected feature-gap inventory
still records 9 explicit rejections; that inventory is not a coverage measure.


### Explicit UNIQUE indexes and replacement conflicts (2026-10-24)

Single-column explicit UNIQUE indexes now retain their uniqueness flag in Core
metadata, canonical CREATE INDEX SQL and both physical decoders. The canonical
printer/parser inverses include that flag. Existing implicit primary indexes
keep their separate primary-key interpretation. UNIQUE comparison uses exact
BINARY SQL value ordering: INTEGER/REAL numeric equals conflict, TEXT/BLOB
storage classes stay distinct, and multiple NULLs are allowed.

Core INSERT, point/general UPDATE, and index creation check uniqueness before
returning a changed table. The SQL INSERT OR REPLACE route allocates a rowid
against the original table, deletes every conflicting primary/unique-key row,
then inserts the complete row through one atomic Core trace. It counts the
inserted row once. The older direct-upsert correspondence now explicitly
requires no explicit UNIQUE indexes; its claim was narrowed instead of being
silently applied to a multi-row replacement. Component proofs establish NULL
non-conflict and the successful INSERT's unique-key freshness. Complete SQLite
constraint semantics remain differential evidence.

Frozen Lean/Main SHA-256:
`666d6cc22383902dcd3a84e029b99a6e9ef891cd7c95a9ec030a758214b8ded3`.
Fresh seed 353601 passed **2,268 statement outcomes**, including **897 matching
errors**, in **12 variants**: both file modes, explicit/implicit rowids, and
Lean/SQLite-512/SQLite-4096 origins. Every outcome checks independent SQLite
reads, raw storage values, uniqueness flags, integrity, Lean reopening and
unchanged main/WAL bytes after errors. Seed 353602 passed **832 rowid UPDATE
regressions**, including **304 matching errors**. Reports are
`docs/validation/sqlite-unique-index-20261024.json` and
`docs/validation/sqlite-unique-rowid-regression-20261024.json`.
Full build, **182 executable tests**, **992 registered headline theorems**, both
audits and the expanded reverse matrix (**61 accepted, 2 declared unsupported**)
passed. The selected gap inventory has 8 explicit rejections, 19 matches and
1 both-reject; this is not a whole-SQLite compatibility rate.

Multi-column, partial and expression indexes, column/table UNIQUE declarations,
non-BINARY collations, other conflict policies and broader schema-name rules
remain separate work. Uniqueness checks currently scan logical rows; large
unique-index creation can do quadratic comparison work.


### Schema namespace, index bindings and no-op creation (2026-10-24)

CREATE TABLE/INDEX now checks the shared table/index namespace, index names
across tables, and reserved sqlite_ object names. IF NOT EXISTS returns the
unchanged state for an existing object of the appropriate kind. Index creation
resolves its target table before the name check, then skips expression binding
for an existing index, matching SQLite's missing-table/missing-column distinction.
Index column binding admits actual columns only: implicit rowid aliases and
qualified index operands are rejected, while real rowid-named columns work.
Both file engines skip publication for successful schema no-ops.

The initial diagnostic found **62 discrepancies in 92 cases**, including
accepted namespace collisions which produced invalid catalog images. That
negative report remains in
`docs/validation/sqlite-schema-admission-negative-20261024.json`.
At frozen Lean/Main SHA-256
`4df6f624a3645e30e934c6ec0bde45f346f1c7b82ecbc55fa97b36a73a0aad2c`,
fresh seed 353612 passed **652 cases**, including **482 matching errors** and
**72 no-ops**, across both file modes. Independent SQLite readers check exact
object identities, table/index metadata and integrity. Main/WAL bytes are
unchanged after errors and no-ops. The corpus uses implicit-rowid tables; it
makes no claim about table-constraint or qualified-schema syntax. Seed 353613
also passed **1,068 UNIQUE regressions**, including **434 matching errors**.
Reports are `docs/validation/sqlite-schema-admission-20261024.json` and
`docs/validation/sqlite-schema-unique-regression-20261024.json`.
Full build, **183 executable tests**, **994 registered headline theorems** and
both audits passed. New component theorems identify the unchanged state/result
of skipped table and index creation. Direct creation correspondence now states
that name preparation admitted an actual creation. The existing diagnostic
inventory remains at 8 explicit feature rejections, not a coverage percentage.


### Aggregate result expressions and operator precedence (2026-10-24)

Ordinary aggregates can now feed scalar result expressions, including arithmetic,
CASE, casts, scalar functions and IN. Bound aggregate terms are accumulated
before the output template runs. A positive OFFSET skips scalar output evaluation
but preserves aggregate-step/finalization errors; LIMIT zero still skips both
after binding. SELECT without FROM aggregates its single implicit empty row,
or no input rows when WHERE is false, and emits the normal empty aggregate row.
Bare source-column results, grouping expressions, HAVING and aggregate ORDER BY
remain separate work. The new registered component theorem proves accumulator
array length; it is not a complete SQL equivalence theorem.

Fresh differential cases exposed three parser defects: concatenation bound below
arithmetic, IS NULL consumed its right operand before subsequent arithmetic,
and relational comparisons shared equality/LIKE precedence. A wider operator
corpus also found BETWEEN upper-bound associativity and rejected NULL-test/IS
DISTINCT FROM spellings. The parser now follows the pinned parse.y precedence
for these operators, and independent token certification accepts ISNULL,
NOTNULL, NOT NULL, IS DISTINCT FROM and IS NOT DISTINCT FROM. Parenthesized
NULL tests remain checked against their original source tokens.

The initial operator corpus found **376 discrepancies in 3,008 outcomes**.
Those results and all three aggregate-discovered parser failures are retained in
`docs/validation/sqlite-operator-precedence-negative-20261024.json` and the
`sqlite-aggregate-results-*-negative-20261024.json` reports.
At frozen Lean/Main SHA-256
`5410ea4354ccdf59062a73dd531456093fb49e5159fd33e00a56c54f2cb5e215`,
fresh seed 353627 passed **3,616 aggregate-result cases** (**378 matching errors**),
seed 353631 passed **6,704 operator cases** (**54 matching errors**), and seed
353628 passed **1,086 aggregate-argument regressions** (**126 matching errors**).
Each suite compares exact CLI bytes and explicitly generated typeof values on
independent images in both file modes; every main/WAL byte must survive reads
unchanged. Error wording is not compared. The existing **1,120 scalar cases**
also passed. Reports are `sqlite-aggregate-results-20261024.json`,
`sqlite-operator-precedence-20261024.json`, `sqlite-aggregate-results-regression-20261024.json`
and `sqlite-aggregate-results-scalar-regression-20261024.json` under
`docs/validation/`.

The full build, **185 executable tests**, **995 registered headline theorems**,
both audits and **61 accepted / 2 declared-unsupported reverse cells** passed.
These are bounded differential results and component proofs, not a percentage
of the entire SQLite language or a claim of complete database/WAL equivalence.


### Boolean keyword binding and IS truth tests (2026-10-24)

The parser preserves TRUE/FALSE as private keyword markers until source-column
binding. Parentheses preserve the keyword; unary plus and arithmetic produce
ordinary expressions. IS/IS NOT uses two-valued truth testing only for an
unshadowed boolean keyword on its right. Real source columns named true/false
bind first, including their affinities, and are retained in predicates,
aggregate inputs and assignments. Constant/index search planning cannot treat
such a column as the integer 1 or 0. INSERT VALUES remains source-free.
The independent grammar accepts the markers only for actual TRUE/FALSE tokens;
calling a private marker as a SQL function is rejected. The legacy conformance
engine was adjusted to the shared parser representation; production execution
still exclusively uses Core. New component theorems cover NULL truth tests and
shadowed-keyword binding.

The initial read-only corpus had **578 discrepancies in 1,372 outcomes**.
At frozen Lean/Main SHA-256
`7851150c35cfaf2610a1d14c84aabc14480d9db31d5e98379511a1d0fa50d6b5`,
fresh seed 353641 checked **2,368 read/write outcomes** in both file modes:
**2,364 matched**, including **18 matching errors**, while **four remained explicit
rejections**. Those four involve CAST of an invalid-UTF-8 BLOB to TEXT through
a shadowing column; the scalar TEXT representation still rejects this preexisting
gap. The report retains the failures without filtering or normalization; this
is not an all-passing compatibility claim. Successful writes are independently
read by SQLite and integrity-checked, and failed writes preserve main/WAL bytes.
Reports are `docs/validation/sqlite-boolean-keywords-negative-20261024.json`,
`sqlite-boolean-keywords-development-20261024.json` and
`sqlite-boolean-keywords-20261024.json` in the same directory.

The **1,120 scalar regressions**, **1,616 fresh aggregate-result regressions**
(**254 matching errors**), full build, **186 executable tests**, **997 registered
headline theorems**, both audits, and **61 accepted / 2 declared-unsupported
reverse cells** passed. The invalid-UTF-8 TEXT conversion failures remain the
next implementation target; broader alias, join, grouping and collation behavior
is outside this boolean corpus.
