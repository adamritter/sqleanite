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

The latest raw-TEXT checkpoint below supersedes earlier invalid-UTF-8 TEXT
rejection notes. Historical negative reports are retained without alteration.

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


### Byte-preserving TEXT and shell control escaping (2026-10-24)

The scalar value representation now retains invalid UTF-8 TEXT as its original
bytes, alongside the existing valid-string representation. Both have SQLite
storage class TEXT. CAST, concatenation, comparison and numeric conversion keep
those bytes through Core records. String operations implement SQLite's distinct
byte-scanning rules: character spans for length/substr, raw matching for instr
and replace, charset spans for trim, permissive decoding for unhex/unicode,
and ASCII-only case conversion. char can emit the surrogate byte sequences
produced by the pinned implementation. No Unicode repair is applied.

A separate pure CLI renderer implements the pinned shell's default control-byte
escaping, including first-NUL termination and the TAB/LF/CRLF exceptions. This
changes printed output only; storage and expression values retain original
bytes. The initial raw corpus retained **994 storage discrepancies** across
1,072 expressions. After value handling was fixed, all **2,892 stored results**
matched, while **476 CLI differences** exposed the missing shell escaping.
These negative reports remain in `sqlite-raw-text-negative-20261024.json` and
`sqlite-raw-text-cli-negative-20261024.json` under `docs/validation/`.

At frozen Lean/Main SHA-256
`a29c65470d15be4bbfc782ec86d0171ecbd7952078bc5d75908369387c901ffe`,
fresh seed 353651 passed **5,180 expressions** in both file modes, with exact
CLI bytes, stored classes, original TEXT/BLOB bytes and REAL bits. Every result
was stored and independently read; integrity checks passed. SQL execution uses
the pinned SQLite **3.53.4** CLI; the independent storage observer is Python's
SQLite **3.45.1**, recorded explicitly in the report. Invalid sequences, NUL,
control characters, surrogate/out-of-range encodings and numeric prefixes are
included. Error wording is outside this comparison.

Fresh regressions also passed **1,968 boolean read/write outcomes** (**18 matching
errors**), **1,120 scalar cases**, **3,541 text-function cases** (**19 matching
errors**), and **6,626 stored pattern results**, **40 pattern queries** and
**24 matching pattern errors**. The four earlier boolean-corpus rejections of
invalid TEXT now succeed. Reports use the `sqlite-raw-text-` prefix under
`docs/validation/`. That checkpoint retained the explicit result-size rejection
`length(zeroblob(1000000))`; the later large-value checkpoint below removes it.
The full build, **187 executable tests**, **1,001 registered headline theorems**,
both audits and **61 accepted / 2 declared-unsupported reverse cells** passed.

These results establish the tested byte-handling behavior, not complete SQL or
file interoperability. UTF-16 database encoding, live SQLite WAL-reader
coordination, general SQL/name binding and the other recorded gaps remain work.


### Quoted identifiers and single-source scope checks (2026-10-24)

Quoted column tokens now bind as identifiers throughout row expressions,
aggregates and assignments. The pinned CLI has DQS fallback disabled, so unknown
quoted names are errors rather than string literals. ORDER BY column terms,
GROUP BY columns and direct grouped outputs share the binder. Quoted markers
are not function calls for SQLite's parser-level zero-AND simplification.
TRUE/FALSE column shadowing continues to use the same binding pass.

SELECT, UPDATE and DELETE validate source/alias scope before lowering to direct
Core commands. The check also covers the reopened cold page reader and persisted
index recognizer, so missing qualifiers cannot disappear on a fast path or under
LIMIT zero. The initial read corpus retained **728 differences in 1,052 outcomes**
in `docs/validation/sqlite-quoted-names-negative-20261024.json`: both rejected
valid quoted columns and incorrectly accepted qualifiers were present.

At frozen Lean/Main SHA-256
`a8787004bacbb09a2e39d30cb5c15f7026fae2a89d6065b4d1a8ff0a7db23b39`,
fresh seed 353661 passed **2,364 read/write outcomes**, including **576 matching
errors**, on independent files in both modes. Reads preserve all main/WAL bytes;
rejected writes preserve the input image. Successful writes are independently
read and integrity-checked by pinned SQLite 3.53.4. The corpus includes quoted
columns, predicates, aggregate arguments, group keys, aliases, qualified stars,
empty tables, LIMIT zero and primary-key searches. Exact CLI bytes and rejection
status are compared; error wording is not. The development report is kept
separately from this final evaluation.

Fresh regressions passed **1,668 boolean read/write outcomes** (**18 matching
errors**), **976 aggregate-result cases** (**170 matching errors**), **166 UPDATEs**
plus **18 expected errors**, **228 DELETEs** plus **16 matching errors**, transaction
rollbacks and **1,120 scalar cases**. Reports use `sqlite-quoted-` under
`docs/validation/`. The full build, **188 executable tests**, **1,003 registered
headline theorems**, both audits and **61 accepted / 2 declared-unsupported reverse
cells** passed. The direct read/write correspondence relations now explicitly
require source-name admission; syntax theorems describe the bound identifier
forms without asserting complete SQLite name resolution.

Output-alias resolution, ordinal and arbitrary-expression ordering, general
GROUP BY expressions/HAVING, quoted function-call parsing, schema-qualified
names and the previously recorded SQL/file/WAL gaps remain separate work.


### ORDER BY expressions, result aliases and positions (2026-10-24)

Single-source scalar SELECTs now resolve ORDER BY result aliases and positional
integers after star expansion. A top-level alias takes precedence over a source
column; inside an expression, source columns take precedence and otherwise an
output alias can supply its expression. Ordinal recognition follows the pinned
32-bit literal/unary rules, so large integer sort constants are not positions.
Ordinary expressions, BINARY collation wrappers, multiple directions and stable
ties use the Core expression sorter. The direct Core command and cold/persisted
read paths share resolved ordering, including aliases that shadow source names.
Source-free scalar SELECTs bind ordering expressions but do not execute an
unnecessary sort over their single implicit input row.

The bounded sorter follows SQLite's LIMIT+OFFSET candidate behavior. It computes
sort keys before admitting an ordinary output row to a full candidate set; rows
later evicted have already evaluated their outputs. DISTINCT computes each
output before duplicate elimination. Primary-key order and known single-row
searches retain their scan path. These choices matter for errors such as integer
abs overflow, beyond merely producing the right sorted successful rows.

The initial corpus retained **736 differences in 1,374 outcomes**. An expanded
intermediate corpus retained **38 BINARY-wrapper rejections in 1,608 outcomes**.
Both reports remain under `docs/validation/` as
`sqlite-order-expression-negative-20261024.json` and
`sqlite-order-expression-binary-negative-20261024.json`.
At frozen Lean/Main SHA-256
`be7f18563e31364f2a7c8ceb68fa017525e0df60ab37858a5ab9e109219378c9`,
fresh seed 353671 passed **2,764 ordering cases**, including **848 matching
errors**, in both file modes. Cases vary data, output/source name collisions,
positions, numeric storage classes, NULLs, limits, offsets and overflow placement.
Exact CLI bytes and rejection status are compared, and reads preserve main/WAL
bytes. Error wording and equivalence to every SQLite planner choice are outside
this comparison.

Fresh regressions passed **12,000 DISTINCT/order queries** across both modes and
before/after index creation, **290 LIMIT/OFFSET cases** (**18 matching errors**),
**1,404 name-binding read/write outcomes** (**576 matching errors**), **916
aggregate-result cases** (**178 matching errors**) and **1,120 scalar cases**.
The full build, **189 executable tests**, **1,005 registered headline theorems**,
both audits and **61 accepted / 2 declared-unsupported reverse cells** passed.
Reports use the `sqlite-order-` prefix under `docs/validation/`.

A larger DISTINCT stress configuration (2,400 input rows, 9,600 queries per phase)
timed out in its first query subprocess after 180 seconds. It has no completed
phase result and is not counted as passing. Its source/executable/harness hashes
and diagnostic are retained in `sqlite-order-distinct-timeout-20261024.json`.
The passing DISTINCT run used a fresh seed and 750 input rows. No throughput or
unbounded scalability claim follows from these results.

Explicit NULLS FIRST/LAST, NOCASE/RTRIM ordering, general aggregate/group ordering,
compound-query ordering, result aliases outside ORDER BY, and the existing
SQL/database/WAL gaps remain separate work. The new registered component proofs
cover zero-LIMIT suppression and stable insertion length, not the entire SQLite
sorter or resolver.


### Ordering collations and explicit NULL placement (2026-10-24)

ORDER terms carry explicit NULLS FIRST/LAST through parsing and independent
token certification. Default placement can retain the direct Core ordering path;
other cases use the expression sorter. Its NULL rule is independent of ascending
or descending comparison. NOCASE and RTRIM port the pinned main.c byte
comparators: NOCASE folds ASCII only, stops its prefix comparison at NUL, then
uses original byte lengths; RTRIM removes trailing byte 0x20 only. BINARY,
numeric storage classes, raw TEXT and BLOB ordering retain their existing rules.

Sort-key collation metadata propagates left first, with an outer COLLATE taking
precedence. Metadata is erased only through operations whose values do not
depend on it. Nested collated comparisons, IN, CASE and scalar min/max/nullif
still require their own scalar support; column declarations with non-BINARY
collations and general collated DISTINCT/grouping are not added here. Non-default
NULL ordering on the separate join path remains explicitly rejected. The legacy
conformance interpreter was updated for the shared NULL-placement field, while
public execution remains entirely on Core.

Further probes exposed parser-phase ordering behavior: a zero-AND folded before
ORDER resolution becomes invalid position zero, and the pinned COLLATE node
does not propagate its child's EP_HasFunc flag. The scalar preparation pass now
tracks that flag boundary, and ORDER resolution prepares before recognizing
positions. An outer used collation can override an unknown inner name. The
initial modifier corpus retained **534 differences in 748 outcomes**; a targeted
fold/override probe retained **10 differences in 16 outcomes**. Both negative
reports and the separate development run remain under `docs/validation/`.

At frozen Lean/Main SHA-256
`a8020e51723da577e1552ac9a112e1d7fe88a6efc9315ac64fa4a13d7c2ac81d`,
fresh seed 353681 passed **1,564 modifier cases** (**118 matching errors**),
including raw bytes, NULs, ASCII/non-ASCII case pairs, numeric classes, aliases,
limits and offsets. Exact CLI bytes and rejection status match pinned SQLite
3.53.4 in both modes; read-only main/WAL images remain unchanged. Error wording
is not compared. Fresh regressions passed **2,364 ordinary ordering cases**
(**774 matching errors**), **1,568 boolean read/write outcomes** (**18 matching
errors**), **7,200 DISTINCT/order queries** across both modes and index states,
and **1,120 scalar cases**. Reports are `sqlite-order-modifier-*.json` and
`sqlite-modifier-*-regression-20261024.json` under `docs/validation/`.

The full build, **190 executable tests**, **1,009 registered headline theorems**,
both audits and **61 accepted / 2 declared-unsupported reverse cells** passed.
New component proofs cover self-comparison, NOCASE NUL behavior, RTRIM suffix
removal and the COLLATE function-flag boundary. These are not whole-SQLite
refinement theorems. The preceding DISTINCT stress timeout and other recorded
SQL/database/WAL gaps remain unresolved.


## Large values, leaf packing and lock contention (2026-10-24)

The shared scalar/physical value limit now uses the pinned default
`SQLITE_MAX_LENGTH=1000000000`. Physical TEXT and BLOB bounds are inclusive at
that value. HEX, ASCII case conversion, quoting, replacement and concatenation
check the relevant result/allocation sizes before constructing expanded output;
the contextMalloc functions account for their terminating byte. This ports the
value-size limit, not every SQLite allocation or encoded-row limit.

The initial differential retained **46 mismatches** at source
`a8020e51723da577e1552ac9a112e1d7fe88a6efc9315ac64fa4a13d7c2ac81d`, including
scalar results, writes and reads of SQLite-created large values. The expanded
suite then exposed **three foreign-file update rejections** at source
`2627dfd5fafcad521419587acd19daf6ab39e27b9f50fbf922efa3038c494d8d`.
Reducing a chunk to one row was insufficient: the compatibility 2-3 tree could
still put two large local payloads on one leaf. `SingletonPageTree` now builds
single-entry leaves for capacity-one chunks, groups levels in twos/threes and
uses the existing root-validity checker. Its entry-preservation proofs feed the
existing physical encoder correspondence; it performs no value-side repair.
Narrower chunks retain their existing builder. Executable regressions exercise
134 tree sizes and 64 row-count/width combinations.

The unit run also exposed a writer-lock TOCTOU race: a released owner file
could disappear between checking and reading it. Owner reads now tolerate that
specific disappearance; a failed mkdir followed by a disappeared directory
retries when the error was EEXIST. Other IO failures still propagate. This fixes
the observed private writer-lock race; it does not implement SQLite SHM locks.

Final production source hash:
`26e8c3fe471cc29bfa2cacd69899b10d4bef041ee79b6a7e87531432456ff146`.
Fresh checkpoint evidence:

- Seed 353701: **128 SQL outcomes**, including **6 matching oversize errors**,
  with original million-byte boundary cases and seeded values above it.
- Seed 353704: **104 SQL outcomes**, including **6 matching oversize errors**,
  and independently stored values exceeding **4,000,000 bytes**. Both file modes
  cover TEXT, BLOB and malformed TEXT, reopen, CREATE INDEX, UPDATE and DELETE.
- SQLite-created **512-, 4096- and 65536-byte-page** files are read without
  modification, then updated in both modes. Complete stored-byte hashes and
  storage classes match the independent SQLite observer, with integrity checks.
- Seed 353702: **512 concurrent subprocess insertions** (16 rounds of 16 writers
  per mode), complete row equality against the expected seeded rows, integrity
  checks and released private lock directories.
- Seed 353703: **2,541 text/blob function cases**, **19 matching errors**, and
  the previously rejected million-byte zeroblob query now passes. The scalar
  regression passes **1,120 cases** and **6 matching errors**.
- Full build: **250 jobs**; **192 executable tests**; **1,015 registered headline
  theorem audits**; live-path audit; **61 accepted / 2 declared unsupported**
  reverse-direction cases.

Reports are `sqlite-large-*` and `sqlite-process-lock-*` under `docs/validation/`.
The original failures, layout failures and lock-race failure remain separate
negative reports. SQL comparison uses pinned SQLite 3.53.4; the complete stored
byte observer reports its distinct Python SQLite 3.45.1 version. Boundary
arithmetic is checked without allocating a billion-byte payload; this is not an
end-to-end test at the maximum value size. Combined encoded-row maximums,
UTF-16 databases, concurrent SQLite WAL/SHM coordination and the previously
listed SQL gaps remain unfinished. The native adapter and nine host bindings
are unchanged.


## WAL append/index components, not live publication (2026-10-24)

`SQLite.WALIndex` now constructs and validates native-endian 48-byte headers,
duplicated header snapshots, the shorter 4,062-frame first hash region and
subsequent 4,096-frame regions. It prepares ordered mapping/slot writes and
removes an interrupted writer's unpublished mapping suffix. Host byte order is
an explicit argument. `SQLite.WALAppend` parses the last committed frame
position and prepares new full-image frames using the existing salts and
chained checksum. Old committed WAL bytes are retained exactly; incomplete or
uncommitted tails are excluded from the next prefix.

These helpers are exercised through the test executable. **They are not yet
connected to the production writer**, which still replaces the whole WAL. The
existing simultaneous SQLite-reader negative is therefore still unresolved.
The proposed three native OS bindings for range-lock acquire/release and host
byte order, together with their audit allowlist expansion, were rejected by
automatic approval review pending explicit user authorization. No part of that
native/audit change was applied. The current native source and nine-binding
allowlist are unchanged. The pure codecs and their tests proceed independently.

The live `WALRead.decodeFrame` now checks the size of the bounded page slice
instead of traversing every remaining byte of the log for each frame. A complete
32-byte WAL header is admitted by its header decoder; public recovery still
returns no committed snapshot for a header-only file. No timing speedup is
claimed without a separate benchmark.

Final source hash:
`2190c31d04dac82b62f38dd66e3ac9e5fd34092a354fc6b853317f3f523a1af6`.
Fresh seed 353711 passes **24 component append cases** across all eight page
sizes from 512 to 65,536. Pinned SQLite 3.53.4 generates each input and reads the
Lean-produced WAL; complete SQL output bytes and integrity match the independently
updated reference database. Each committed prefix is byte-identical. Clean,
partial and valid-but-uncommitted tails are covered. Opposite checksum order is
an explicitly synthetic re-encoding, independently read by SQLite, not claimed
to be generated by its native writer.

The same run compares native little-endian SHM mapping bytes exactly, with eight
configured interrupted-append split points per file (large split positions are
capped on smaller files). The largest fresh case has **5,198 frames** and crosses
the first region boundary. Big-endian header round-trips are component tests
only, not execution on a big-endian host. The earlier 5,015-frame development
probe is not used as the final-checkpoint result.

Fresh seed 353712 passes **1,024 production-reader recovery outcomes**, including
**64 matching errors**, over frozen SQLite-created WALs with eight page sizes,
both checksum orders and damaged/truncated tails. Full build: **254 jobs**;
**193 executable tests**; **1,020 registered headline audits**; verification and
live-path audits pass. Registered new lemmas cover header/frame byte sizes,
empty-append cleanup and empty-image rejection. They are not a proof of the
concurrent publication protocol or complete WAL-index equivalence.

Reports: `sqlite-wal-components-20261024.json`,
`sqlite-wal-components-recovery-regression-20261024.json` and
`sqlite-wal-component-checks-20261024.json` in `docs/validation/`.


## Quoted function calls and argument admission (2026-10-24)

The production parser and independent token checker now accept function names
in double quotes, brackets and backticks. Single quotes remain string literals.
Scalar DISTINCT is accepted and ignored as in SQLite; aggregate DISTINCT keeps
its existing accumulator semantics. The parser, token checker and scalar
admission enforce the pinned default 1,000-argument maximum. The public CAST
syntax remains the only route to internal cast operations, including when a
user spells a private function name in uppercase or adds DISTINCT.

The initial seed 353720 recorded 612 differences in 884 outcomes at source
`2190c31d04dac82b62f38dd66e3ac9e5fd34092a354fc6b853317f3f523a1af6`.
The expanded final corpus uses fresh seed 353722 at source
`a12f0750ff26b4b0c4183740a0f42c556ed8e47fdf642fc27550d6d2aedf7fc6`:
**1,784 of 1,786 outcomes match**, including 318 matching read errors and six
row-dependent write scenarios across both production file modes. The two
remaining failures are the same `sum(v) OVER ()` query in each mode; window
execution remains unsupported. The harness retains these failures and exits
nonzero. This is not a full-corpus pass or a SQLite-wide compatibility percentage.
Read queries preserve main/WAL bytes. Error matching checks ordinary nonzero
exit status, not exact wording or SQLite error codes.

The final source also passes 916 aggregate-result regression outcomes
(seed 353723, 184 matching errors), the existing 1,120 scalar cases, all 194
executable tests, the 1,021-headline proof build, the host and live-path audits,
and 61 reverse file-format cases with two separately declared unsupported cells.
The scalar regression uses its existing fixed corpus, not new random examples.
The argument-bound theorem covers scalar syntax rejection; executable boundary
cases cover 999, 1,000 and 1,001 arguments. No native code or audit allowlist changed.

Reports are `sqlite-quoted-function-negative-20261024.json`,
`sqlite-quoted-function-20261024.json`, `sqlite-quoted-function-checks-20261024.json`
and the two `sqlite-quoted-function-*-regression-20261024.json` files under
`docs/validation/`. Other SQL and WAL gaps listed above remain outstanding.


## Explicit scalar and aggregate collations (2026-10-24)

The production scalar evaluator now carries BINARY, NOCASE and RTRIM through
comparison, IS, IN, CASE, scalar min/max/nullif, and row-dependent predicates
and writes. COLLATE preserves affinity; unary plus continues to remove it.
The existing parser rewrite of a constant single-item IN list is significant:
it uses comparison collation from both operands, while a multi-item or
row-dependent list uses the left operand. Unused unknown collation metadata is
accepted, but a comparison that needs an unknown collation is rejected before
empty-input/LIMIT shortcuts. The independent token certificate is unchanged.

Expression DISTINCT now compares each output with its own collation and keeps
its original representative. Aggregate argument collations govern DISTINCT
and extrema; aggregate output templates preserve that metadata through lowered
result slots. A non-BINARY comparison operand prevents a BINARY index lookup
and uses the row-expression evaluator. This does not add collated indexes or
stored column collations, which remain separate unsupported schema features.

Initial seed 353730 at source
`a12f0750ff26b4b0c4183740a0f42c556ed8e47fdf642fc27550d6d2aedf7fc6`
recorded 2,560 differences in 2,596 outcomes. Development seed 353731 reduced
that to eight in 2,736 outcomes. A separate eight-case negative caught lost
aggregate-result metadata and missing DISTINCT collation validation; both
were fixed before final evaluation. All negatives are retained.

Final source is
`31e1f4a94d813ace2235c4140b9b15ac9d1151c79f0eccb286d5606764de0aa7`.
Fresh seed 353732 matches **3,252 of 3,260 outcomes**, including 30 matching
errors and six write scenarios. **Eight failures remain:** six grouped-column
queries with explicit COLLATE are rejected, and the NOCASE UNION query returns
the wrong rows in each file mode. The harness includes these failures and
returns nonzero. Scalar success must not be read as compound or GROUP BY
collation compatibility. This checkpoint is not a full SQLite compatibility
claim. Read-only queries preserve main/WAL bytes; matching errors check status,
not message text or exact error codes.

At this same source, seed 353733 passes 864 ordering outcomes (118 matching
errors), seed 353734 passes 916 aggregate-result outcomes (174 matching errors),
and all 195 executable tests, the 1,023-headline theorem build, verification
audit and live-path checks pass. The scalar regression initially stopped on
its obsolete requirement that `coalesce(1,2 COLLATE NOCASE)` be rejected. That
case now joins the positive oracle corpus: all 1,121 cases and six matching
errors pass. Native code and the nine-binding boundary remain unchanged.

Reports use `sqlite-scalar-collation-*20261024.json` and
`sqlite-aggregate-collation-negative-20261024.json` under `docs/validation/`.
The new selector and text self-comparison lemmas are component properties;
they are not a proof of full SQLite expression equivalence.


## Collated column groups and bounded finalization (2026-10-24)

`CoreCollatedGroup` adds one- and multi-column grouping under explicit BINARY,
NOCASE and RTRIM. Group comparison uses original values, including raw TEXT,
NULL and exact INTEGER/REAL equivalence. Key enumeration preserves a first
source representative; the existing last-unique-min/max rule independently
selects the original row used for bare group-key outputs. Count, sum, average,
total and plain-column extrema run over all rows of the collated group.
Source predicates can use the row-expression evaluator. The existing proved
BINARY Core route remains in use for its directly translated shape.

LIMIT bounds the groups whose aggregates are finalized. OFFSET skips only
after finalization, so an overflowing skipped group still fails while an
excluded group after the LIMIT does not. LIMIT 0 validates names, collations
and output shapes without evaluating inputs. This extension does not yet add
general GROUP BY expressions, grouped result templates, aggregate-argument
COLLATE, grouped DISTINCT, ORDER BY or HAVING.

Seed 353740 at source
`31e1f4a94d813ace2235c4140b9b15ac9d1151c79f0eccb286d5606764de0aa7`
recorded 322 differences in 328 outcomes. Fresh final seed 353742 at source
`1483986d381a67d52e16c5e5e4f0dd6b666c9da74508dabe12bcc169b903263e`
matches **1,254 of 1,258 outcomes**, including 12 matching errors. Four retained
failures are grouped ORDER BY and HAVING, each in both file modes. The harness
still exits nonzero. The eight-case scalar collation boundary from the prior
checkpoint is reduced to the two NOCASE UNION failures: fresh seed 353743
matches **2,958 of 2,960 outcomes**, with 30 matching errors and six writes.
The six earlier GROUP BY failures now pass. None of these counts measures
SQLite-wide coverage. Read queries preserve main/WAL bytes; matching errors
compare ordinary exit status, not diagnostics.

Fresh seed 353744 passes 916 aggregate-result regression outcomes, including
180 matching errors. The complete 258-job build, all 196 executable tests,
1,029 registered headline theorems, verification audit and live-path checks
pass. New proofs establish source-row membership, emitted width, zero-LIMIT
behavior and state preservation; they do not prove full SQLite group semantics.
The current group enumeration is not claimed to have SQLite's asymptotic
performance. Native code and its nine-binding audit boundary are unchanged.
Reports use `sqlite-group-collation-*20261024.json` under `docs/validation/`.


## Compound result collations and original representatives (2026-10-24)

UNION, UNION ALL, INTERSECT and EXCEPT now resolve each result column's
collation across arms. The first arm supplying a collation wins, including an
implicit BINARY collation on a stored column, unary plus or CAST. Unused later
unknown collation names do not override it. UNION ALL alone does not require
an otherwise unused collation. BINARY, NOCASE and RTRIM compare original TEXT
bytes alongside numeric storage classes; duplicate removal preserves the
pinned operation's original representative. Stars are expanded and names
bound before resolution. Supported column-only joins participate as well.

The retained initial seed 353750 recorded 232 differences in 1,192 outcomes at
source `1483986d381a67d52e16c5e5e4f0dd6b666c9da74508dabe12bcc169b903263e`.
Final source `772a30c878c89672c1e75aea564ee3ff35b522d3643554d49d115b6cf1e14182`
with fresh seed 353752 matches **1,932 of 1,936 outcomes**, including six
matching errors. The four retained failures are outer compound ORDER BY and
LIMIT in both production file modes; the harness exits nonzero. Read queries
preserve main/WAL bytes. Error matching compares ordinary exit status, not
exact diagnostics. CLI comparison cannot observe text beyond an embedded NUL;
separate Core executable examples check complete representative bytes for
embedded NUL and invalid UTF-8. Those examples are component evidence.

The existing BINARY read and recursive-compound refinement proofs still hold
with their original premises. New proofs establish binding preservation of
explicit collation metadata, absence of that metadata for the translated
BINARY grammar, preservation of input representatives, and BINARY/UNION ALL
specializations. They do not prove full SQLite compound equivalence.
The complete 260-job build, all 197 executable tests, 1,036 registered headline
theorems, verification audit and live-path checks pass. Fresh seed 353754
passes 280 BINARY compound queries plus three matching errors; 61 reverse
file-format cells pass, with two declared unsupported cells. Native code and
the nine-binding boundary are unchanged. Reports use
`sqlite-compound-collation-*20261024.json` in `docs/validation/`.

The fresh scalar/group collation regression at seed 353753 passes all 2,854
read outcomes (30 matching errors) and six writes. This closes the two retained
NOCASE UNION differences in that bounded corpus; it is not SQLite-wide coverage.


## Compound ordering, windows and bounded UNION ALL (2026-10-24)

The production compound path now resolves ORDER BY positions, output aliases
across arms, and structurally matching result expressions. It carries
collations, direction and NULL placement through stable input sorting and the
pinned left/right merge rules. Set operations extend the merge key with
unmentioned result columns and remove adjacent duplicates under the result
collations. An explicit ORDER BY collation on a set compound sorts its completed
result separately, following SQLite's subquery rewrite. The binder expands
stars and includes the supported column-only join output.

LIMIT/OFFSET applies to the entire compound. UNION ALL propagates the remaining
window into its arms; unused arms and skipped plain output expressions are not
evaluated. Names and widths are validated for every arm, even with LIMIT 0.
Skipped plain rows are counted using their predicate and a constant projection
before the retained output scan; supported scalar functions are deterministic.
This can repeat predicate work and is not an asymptotic performance claim.
An empty left INTERSECT/EXCEPT input does not evaluate right-side values.
Aggregate/group/join outputs use their existing leaf executors followed by
result-slot sorting. This does not add general grouped ORDER BY or HAVING.

Initial seed 353760 retained 1,238 differences in 1,400 outcomes at source
`772a30c878c89672c1e75aea564ee3ff35b522d3643554d49d115b6cf1e14182`.
Fresh final seed 353762 at source
`c4af3c7bc1002874a25af3883fc4694b7670cc2c5d1c68e7e276719df46c6407`
matches **2,110 of 2,112 outcomes**, including 132 matching errors. Two failures
remain: `SELECT 1.0 UNION SELECT 2 ORDER BY 1.00` succeeds here but SQLite rejects
it, in each file mode. The AST currently loses the different REAL token
spellings. The report retains both failures and the harness exits nonzero.
The development report also retains the earlier join-binding counterexample.
These are bounded corpus counts, not a SQLite-wide compatibility percentage.
Read queries preserve main/WAL bytes; errors compare ordinary exit status.

Fresh seed 353763 passes all 1,636 compound-collation outcomes, including its
previous four ORDER BY/LIMIT failures and six matching errors. Seed 353764
passes 1,804 single-source ordering outcomes (598 matching errors); seed 353765
passes 290 LIMIT/OFFSET outcomes plus 18 separately checked matching errors.
The full 262-job build, all 198 executable tests, 1,043 registered headline
theorems, verification and live-path audits pass. New proofs cover window and
merge membership, sorting permutation, zero LIMIT and state preservation; they
do not establish full SQLite merge/evaluation equivalence. Existing BINARY
read refinements retain their premises. Native code and the nine-binding audit
boundary are unchanged. Reports use `sqlite-compound-tail-*20261024.json`.


## Preserved REAL literal spelling (2026-10-24)

A literal AST node can now carry its original REAL token spelling. The parser
retains it, and the independent token checker rejects a changed or omitted
spelling. Scalar evaluation ignores this syntax metadata; expression identity
compares it. As a result, compound ORDER BY distinguishes `1.0`, `1.00`, `1e0`
and `1E0`, including inside functions, CAST, CASE and alias substitutions.
The two retained failures from the compound-tail checkpoint are closed.
This change does not preserve lost integer token spellings or add numeric
underscore syntax; hexadecimal integer edge cases remain separate work.

The initial seed 353770 at source
`c4af3c7bc1002874a25af3883fc4694b7670cc2c5d1c68e7e276719df46c6407`
recorded 374 differences in 1,772 outcomes. Fresh final seed 353772 at source
`a2b4018acd65cfddaa1f9bdb2f1a573382b00fe413d29202a93c1ea3074297b6`
passes **all 3,692 outcomes**, including **2,116 matching errors**. These errors
are mostly intentionally different expression spellings, not successful reads.
The harness compares exact CLI bytes or ordinary positive error status and
checks that read queries preserve main/WAL bytes. It does not compare error
wording or SQLite error codes. No SQLite-wide compatibility percentage follows.

Fresh seed 353773 passes all 2,012 compound-tail regression outcomes, including
134 matching errors. The existing fixed scalar corpus passes 1,121 cases plus
six matching errors, checking storage classes, binary64 bits and raw TEXT/BLOB
bytes. All 199 executable tests, the full 262-job build, 1,045 registered
headline theorems, verification audit and live-path checks pass. Executable
adversarial cases reject altered and missing REAL spelling in a proposed AST.
New lemmas show that literal spelling does not change scalar evaluation and
that REAL syntax identity compares the stored spellings; they are component
properties, not a proof of complete SQLite expression equivalence. Native code
and its nine-binding audit boundary are unchanged. Reports use
`sqlite-literal-spelling-*20261024.json` under `docs/validation/`.


## Numeric token syntax and signed hexadecimal boundaries (2026-10-24)

The numeric scanner now accepts a single underscore between adjacent decimal
or hexadecimal digits and rejects malformed separators, incomplete exponents
and identifier text attached to a number. Hexadecimal values within 64 bits
use signed two's-complement interpretation; insignificant leading zeros do not
count against that range. Numeric tokens retain their spelling, and the AST
retains the normalized spelling except for SQLite's compact positive 31-bit
integers. REAL identity still distinguishes spellings after underscores are
removed. Large integer identity now preserves those distinctions as well.
Stored-string CAST and numeric coercion continue to use their own rules.

Literal preparation preserves the decimal signed INTEGER minimum, including
parentheses and unary plus. A directly negated minimum hexadecimal literal is
rejected before evaluation, while a COLLATE-wrapped operand uses ordinary
runtime subtraction. The independent token checker verifies normalized spelling,
parsed value and numeric storage class; a forged REAL for a small INTEGER token
is rejected. Literal-value and source-spelling consistency guards the signed
minimum special case. Source metadata is therefore relevant to numeric-literal
preparation as well as expression identity.

Initial seed 353780 at source
`a2b4018acd65cfddaa1f9bdb2f1a573382b00fe413d29202a93c1ea3074297b6`
recorded 656 differences in 950 outcomes. The first large checkpoint passed
5,358 outcomes, but a subsequent independent preparation probe found that
`0 AND 0x10000000000000000` was rejected too early. SQLite folds that unused
literal away before reporting its range error. The two file-mode failures in
the eight-case probe are retained, along with the earlier passing checkpoint;
range rejection now occurs after expression preparation. Malformed numeric
syntax still fails lexically, and an oversized LIMIT/OFFSET hex token is rejected.

Final source is
`231e5c80c96573542e5e41dd8d31d5193dd659d25d84e41dbf6e73234117dcee`.
Fresh seed 353784 passes **all 5,368 read outcomes**, including **84 matching
errors**, plus **eight write scenarios**. After each write, the harness compares
typed/quoted stored values and SQLite independently runs integrity_check on the
Lean database. Reads preserve main/WAL bytes. Error matching checks ordinary
positive status, not diagnostics or exact SQLite error codes. Fresh seed 353785
passes all 2,672 literal-spelling outcomes, including 1,810 matching errors.
The existing fixed scalar regression passes 1,121 cases plus six matching errors,
with storage classes, binary64 bits and raw TEXT/BLOB comparisons.

The complete 264-job build, all 200 executable tests, 1,051 registered headline
theorems, verification audit and live-path checks pass. New component proofs
bound signed hexadecimal interpretation, characterize its two halves, reject
a trailing separator, and cover the two signed-minimum preparation rules.
They do not prove complete tokenizer or SQLite equivalence. These bounded
corpus results do not establish SQLite-wide compatibility. Native code and its
nine-binding audit boundary are unchanged. Reports use
`sqlite-numeric-literal-*20261024.json` under `docs/validation/`.


## Ungrouped aggregate ORDER BY (2026-10-24)

Singleton aggregate results now bind and validate ORDER BY aliases, ordinals,
source columns, collations and scalar expressions. Aggregate calls in the order
terms join the result accumulators and are finalized before OFFSET. SQLite does
not evaluate the outer scalar sort keys for this one-row result; consequently
`ORDER BY abs(-9223372036854775808)` succeeds, while placing that expression
inside a SUM argument reports overflow on nonempty input. LIMIT zero validates
names and expression structure but skips accumulation. Bare source columns in
unused sort keys are erased only after binding; aggregate arguments are preserved.

Source-free scalar SELECT has a separate SQLite behavior: aggregate calls in its
unused ORDER BY are validated but never accumulated. A table-backed scalar SELECT
still rejects aggregate-only ordering. Aggregate result preparation also folds
`0 AND` before admitting an otherwise oversized hexadecimal literal. The output
projection is unchanged when auxiliary ORDER BY aggregates are appended.

Initial seed 353790 recorded 1,416 differences in 1,806 outcomes. Development seed
353791 reduced this to 590 differences in 1,926 outcomes; a separate six-outcome
preparation probe retained the source-free and oversized-literal failures before
they were fixed. These negative reports are preserved.

Final source is
`2b3e244e5c8915632e996f7c52af95531a6d4b17694f5e2db7d7d5e5d87c6186`.
Fresh seed 353792 contains **2,298 outcomes with 876 remaining differences**, all
involving HAVING. The explicitly named **non-HAVING subset passes all 1,120
outcomes**. The full report retains every failure and the harness exits nonzero;
this is not a passing full aggregate-tail corpus. Both production file modes
compare exact CLI bytes or ordinary positive error status and preserve all
main/WAL bytes. Error wording and exact SQLite error codes are not compared.

Fresh seed 353793 passes all 1,016 aggregate-result regression outcomes, including
178 matching errors. Fresh seed 353794 passes all 1,804 ordering regression
outcomes, including 618 matching errors. The fixed scalar regression passes
1,121 cases plus six matching errors. The full 266-job build, all 201 executable
tests, 1,053 registered headline theorems and verification audit pass.
Correction: the live-path audit exited 1 because its numeric-aggregate check
still required the previous direct preparation call. The original checkpoint
summary incorrectly inferred success from the log tail. The complete failed
log is retained; the grouped-expression checkpoint updates and reruns this check. Two new component lemmas preserve the output projection and aggregate
arguments; they do not establish general SQLite equivalence. Native code and its
nine-binding audit boundary are unchanged. Reports use
`sqlite-aggregate-order-*20261024.json` and
`sqlite-aggregate-tail-negative-20261024.json` under `docs/validation/`.


## Ungrouped HAVING and retained aggregate source rows (2026-10-24)

Ungrouped HAVING now resolves output aliases with source-column precedence,
registers aggregates after result and ORDER BY aggregates, and tests its predicate
after finalizing every accumulator. HAVING precedes OFFSET and scalar output
evaluation. Thus an overflowing SUM still fails under HAVING zero, while a scalar
result overflow is suppressed when HAVING rejects the row. LIMIT zero still
validates the statement and skips input evaluation. A nonaggregate SELECT with
HAVING remains an error.

The aggregate template compiler now has an explicit bare-column mode. It binds
source references to private positional slots, separately from aggregate slots,
and retains source affinity for comparisons. This also adds bare-column aggregate
outputs and expanded stars. Private slot names supplied by users do not bypass
binding; actual tables using those names remain usable. Empty input provides NULL
source values. Without MIN/MAX the first source row is retained. Unique MIN/MAX
calls are considered in result, ordering and HAVING order. Each performed step
sets the shared replacement flag; DISTINCT duplicates skip that update, so a
skipped duplicate can retain a preceding step's flag. Explicit argument collations
remain part of aggregate identity. Deterministic extreme arguments are currently
reevaluated for representative selection after aggregate finalization.

Final source is
`c6ed74e8976cb59eb138c3fda506bcc6106db35cfb6627f6df5e033a0af56b16`.
Fresh seed 353802 has **1,918 outcomes, with two remaining grouped-HAVING
failures**; its explicitly named ungrouped subset passes all 1,916 outcomes.
Fresh seed 353803 has **2,298 aggregate-tail outcomes, with the same two grouped
failures**; all 2,296 ungrouped outcomes match, including 526 ordinary errors.
Every failure remains in its report and both full harness runs exit nonzero.
Development seeds 353800 and 353801 are retained separately. CLI bytes and
positive error status are compared in both production file modes, and reads
must preserve all main/WAL bytes. Exact error codes and wording are not compared.

Fresh seed 353804 passes all 1,116 aggregate-result regression outcomes, including
200 matching errors. Fresh seed 353805 passes all 2,694 explicit-collation reads
and six writes, including 30 matching errors. The fixed scalar regression passes
1,121 cases plus six matching errors. All 202 executable tests, the complete
268-job build, 1,055 registered headline theorems and verification audit pass.
Correction: the live-path audit still exited 1 on the stale numeric-aggregate
call-chain check. The original summary incorrectly reported it as passing.
The complete failed log is retained; the grouped-expression checkpoint repairs
the structural check and reruns it. New component lemmas characterize retained-row selection and an
absent HAVING predicate; they are not a proof of complete aggregation semantics.
Grouped HAVING/ordering and general grouping expressions remain subsequent work.
No SQLite-wide compatibility percentage follows from these bounded corpora.
Native code and its nine-binding audit boundary are unchanged. Reports use
`sqlite-aggregate-having-*20261024.json` under `docs/validation/`.


## Grouped expressions, HAVING, ordering and DISTINCT (2026-10-24)

The general Core grouping path now accepts scalar grouping keys, result aliases
and ordinals, aggregate result templates, retained bare source columns, HAVING,
ORDER BY and DISTINCT. Grouping keeps original key values separately from the
MIN/MAX representative row. Source-free grouping consumes its one implicit row;
a false WHERE produces no group. A checked result shape rejects an impossible
multi-group source-free result rather than dropping rows.

HAVING terms made only from constants and BINARY group keys can move before
grouping; an always-false integer term remains after aggregation, matching the
pinned SQLite implementation. Thus `HAVING NULL` can suppress an overflowing
SUM while `HAVING 0` does not. Grouped WHERE aliases use source-name precedence.
LIMIT zero validates names and expressions before skipping execution. With
natural group order, OFFSET skips scalar outputs after finalization/HAVING and
LIMIT stops further groups. A separate sorter finalizes all groups and applies
bounded output selection; DISTINCT computes output before duplicate removal.

SQLite copies ORDER BY direction flags into equal-length GROUP BY lists even
when their expressions differ. This determines tie order in the later output
sort. Non-column outputs reused by GROUP BY read the saved grouping key, while
bare columns use the retained source row. A separate non-DISTINCT output sorter
can instead reuse its ORDER BY expression as the output payload; DISTINCT keeps
the previously computed output value. These differences are covered with mixed
INTEGER/REAL storage classes and collated-equal original strings.

The initial seed 353810 recorded 384 differences in 438 outcomes. Development
seed 353811 recorded 90 differences in 750 outcomes, predominantly tie ordering.
After that fix seed 353813 passed 1,050 outcomes. The larger independent seed
353815 then found 16 differences in 2,050 outcomes: DISTINCT key reuse and grouped
WHERE aliases. Those negative reports remain; both issues were fixed before the
final checkpoint.

Final source is
`cf7101680a8d4cbe6b74fc408b2607c2f2fa187a5e88243f19a03e59853e3321`.
Fresh seed 353816 passes **all 2,450 grouped-expression outcomes**, including
196 matching ordinary errors. Fresh regressions pass 1,058 collated-group outcomes
(seed 353817, 12 matching errors), 2,298 aggregate-tail outcomes (353818, 546
matching errors), and 1,518 aggregate-HAVING outcomes (353819, 218 matching errors).
These last two corpora now also pass their previously retained grouped-HAVING
cases. The fixed scalar regression passes 1,121 cases plus six matching errors.
Every live-mode comparison uses exact CLI bytes or positive error status; read
queries preserve all main/WAL bytes. Error messages/codes and planner-wide row
ordering are not asserted equivalent.

All 203 executable tests, the complete 270-job build, 1,057 registered headline
theorems and verification audit pass. The live-path audit initially failed its
stale requirement for a direct CoreAggregate preparation call. Its check now
follows the real CoreAggregateHaving/CoreGrouped call chains and verifies their
shared accumulator, representative, HAVING and sorter links. The corrected audit
exits zero. The earlier aggregate ORDER/HAVING summaries incorrectly inferred
success from only the end of the log; those summaries are corrected above and
their complete failed logs are retained. The full reverse-file matrix also
passes: 61 accepted cases and two explicitly unsupported shapes.

New component lemmas cover first-bucket insertion and zero-limit group emission;
they do not prove complete grouped SQL equivalence. The implementation materializes
group buckets and makes no scaling claim. Native code and its nine-binding audit
boundary are unchanged. Reports use `sqlite-grouped-expression-*20261024.json`
under `docs/validation/`. These bounded results do not establish 100% SQLite
compatibility.


## WHERE result aliases and direct-read admission (2026-10-24)

Single-source and source-free WHERE expressions now resolve result aliases with
source-column precedence. Qualified names remain source references, duplicate
aliases select the first result, and substituted expressions are not recursively
resolved against other output aliases. TRUE/FALSE result aliases bind before
boolean evaluation when there is no shadowing source column. Parser-level
simplification precedes substitution, so `0 AND alias` can remove an unused
aggregate alias before it becomes an aggregate-function misuse.

The direct Core query and persisted-query recognizers decline predicates with
pending alias substitutions. The existing expression route resolves and validates
them, including on empty input and LIMIT zero. This prevents a TRUE/FALSE alias
from accidentally becoming a constant predicate in a page-directed read. Grouped
WHERE and aggregate HAVING routes share the same resolver. Aggregate aliases in
ordinary WHERE remain invalid unless parser-level simplification removes them.

Initial seed 353830 at the preceding checkpoint recorded 162 differences in
642 outcomes. Development seed 353831 passes 842 outcomes. Final source is
`2d3b2c789e7010810ef4c385c190e705dc54cb7275c3268abaf46f8249aba0a2`.
Fresh seed 353832 passes **all 1,448 outcomes**, including **788 matching errors**;
the intentionally invalid alias/function cases are therefore not counted as
successful reads. Fresh seed 353833 passes all 1,050 grouped-expression regression
outcomes, including 82 matching errors. Both live file modes compare exact CLI
bytes or ordinary positive error status, preserving main/WAL bytes on reads.
Exact diagnostic wording and SQLite error codes are not compared.

The fixed scalar regression passes 1,121 cases plus six matching errors. All
204 executable tests, the complete 270-job build, 1,058 registered headline
theorems, verification audit and updated live-path audit pass. The new component
lemma shows alias resolution leaves literal values and spellings unchanged;
it is not a proof of complete name-resolution equivalence. Native code and its
nine-binding audit boundary are unchanged. Reports use
`sqlite-where-alias-*20261024.json` under `docs/validation/`.


## Persistent application ID and user version (2026-10-24)

Live rewrites now preserve the existing SQLite application_id and user_version
fields. New databases use application_id zero instead of the private LSQL value.
The existing generated-image counter marker remains, and the generated fast path
now requires default application-owned metadata. Nondefault metadata uses the
proved complete-image/freelist layout, which carries those two fields separately
from schema B-tree bytes and page allocation. The wide bulk optimization declines
that metadata shape and falls back to the existing proved bulk encoder.

Page-size conversion explicitly reads metadata from the original file before
building the replacement image. WAL writes and checkpoints obtain metadata from
the most recent committed page-one overlay, falling back to the main header when
there is no overlay. The same header-layout inverse proof covers the customized
header; no opaque decoder certificate or additional native host binding was added.

At source `2d3b2c789e7010810ef4c385c190e705dc54cb7275c3268abaf46f8249aba0a2`,
all 54 initial metadata write cases differed. The retained report records the
private application ID overwrite and lost nonzero user versions. Development
seed 353841 passes 144 write scenarios. Final source is
`ec0164a8da29c01fd9ad81894233d3215e3916dc6f617a1e7b423aae4d95a7ba`.
Fresh seed 353842 passes **360 write scenarios** over 512/4096/65536-byte foreign
files in both production modes. Fresh seed 353843 passes **132 WAL-overlay
scenarios** with metadata differing from the main header. Fresh seed 353844
passes **108 explicit Lean checkpoint scenarios** from such overlays. These
include signed 32-bit metadata boundaries, new seeded identifiers/versions,
UPDATE, INSERT, index creation and multiple successive writes.

Pinned SQLite creates each input and independently compares the resulting public
metadata PRAGMAs, typed/quoted rows and integrity_check. WAL fixtures use SQLite's
no-checkpoint-on-close configuration; no C connection remains open during the
Lean write. These tests do not establish concurrent WAL compatibility. Raw change
counters, schema cookies and format/version fields are recorded separately and
are not normalized or asserted equal. In particular, the existing fixed change
counter and schema-cookie behavior still require further work. This change
preserves stored metadata; it does not implement SQL PRAGMA statements in Lean.

All 205 executable tests, the complete 270-job build, 1,060 registered headline
theorems, verification audit and updated live-path audit pass. The reverse-file
matrix passes 61 accepted cases and two explicitly unsupported shapes. The fixed
scalar regression passes 1,121 cases plus six matching errors. New component
lemmas identify the application ID and user version emitted by the header layout;
the existing catalog/page-source inverse proofs continue to compile with those
fields parameterized. Native code and its nine-binding audit boundary are
unchanged. Reports use `sqlite-header-metadata-*20261024.json` under
`docs/validation/`. These results do not establish full SQL or file-format parity.


## Ordinary GROUP_CONCAT and STRING_AGG (2026-10-24)

Production Core aggregates now include GROUP_CONCAT with one or two arguments
and STRING_AGG with exactly two. Each row evaluates both supplied arguments,
including NULL-value rows and the first accepted value. NULL values contribute
nothing; NULL separators contribute zero bytes. The current non-NULL row's
separator precedes its value after the first accepted row. Empty input and
all-NULL input return NULL, while an accepted empty string produces TEXT.
Numeric inputs use the pinned scalar rendering, and BLOB/TEXT conversion retains
all bytes, including malformed UTF-8 and embedded NULs. The accumulator checks
the configured byte limit including its terminating byte before appending.

Single-argument DISTINCT keeps the first original representative using its
collation and numeric equivalence before text conversion. Invalid arity, nested
aggregates, unresolved arguments and required DISTINCT collations are rejected
at preparation, including on empty input and LIMIT zero. The existing aggregate
result/group/HAVING/ORDER routes use this accumulator. Aggregate-internal ORDER
BY, FILTER and window execution remain separate work.

The preceding source ec0164a8da29c01fd9ad81894233d3215e3916dc6f617a1e7b423aae4d95a7ba
has 414 differences in the retained 732-outcome baseline, seed 353850. Development
seed 353851 passes 1,212 outcomes. Final source is
`d6ab9d23b818e390185397ed2a67082715d507980b196fa666d781650cd0dc55`.
Fresh seed 353852 passes **2,612 outcomes**, including **1,200 matching positive
error statuses**. Fresh grouped-expression seed 353853 passes **1,150 outcomes**,
including 100 matching errors. These are both production file modes, with exact
CLI bytes for successful reads and no main/WAL changes. Hex projections check
complete bytes independently of the CLI's NUL truncation. Error codes and wording
are not compared; actual near-gigabyte allocation boundaries are not exercised.

All 206 executable tests, the full 272-job build, 1,063 registered headline
proofs, verification audit and live-path audit pass. The reverse-file matrix
passes 61 accepted cases and two declared unsupported shapes. New component
lemmas cover NULL-step neutrality, the first separator's irrelevance to the
accumulator, and the empty result. These are not whole-query equivalence proofs.
Native code and its nine-binding audit boundary remain unchanged. Reports are
`sqlite-string-aggregate-*20261024.json` under `docs/validation/`; these bounded
results do not establish full SQLite compatibility.


## UNISTR and UNISTR_QUOTE (2026-10-24)

Both functions now execute through the production scalar evaluator. UNISTR
accepts the four documented hexadecimal escape forms and doubled backslashes,
rejecting malformed escapes when evaluated. Its byte encoder follows the pinned
func.c/utf.c behavior for surrogates and out-of-range 32-bit values, including
masked four-byte prefixes. It preserves original invalid UTF-8 bytes. A source
NUL stops further escape searches and copies the remaining original suffix;
a NUL produced by a decoded escape does not stop subsequent decoding.

UNISTR_QUOTE preserves ordinary QUOTE behavior for non-text input and text
without control bytes before the first NUL. Text with control bytes uses the
unistr('...') wrapper, lowercase hexadecimal control escapes, doubled quotes
and doubled backslashes. This also truncates at the first source NUL, matching
QUOTE's representability rule. Allocation checks precede quoted output assembly.
These behaviors follow the pinned C source and the public
[core-function definitions](https://sqlite.org/lang_corefunc.html#unistr).

The previous source d6ab9d23b818e390185397ed2a67082715d507980b196fa666d781650cd0dc55
records 422 differences in 490 baseline outcomes, seed 353860. Development seed
353861 passes 1,386 reads and 12 subsequent write scenarios. Final source is
`e0c2cb3cdb827fa3e3860604d890a7c0fd6cc46e01792485a47a7d353124145a`.
Fresh seed 353862 passes **4,186 reads**, including **414 matching positive error
statuses**, and **12 write scenarios**, including four matching failed writes.
Read checks compare complete type/hex results and preserve database/WAL bytes;
write checks compare typed hex readback after each statement, including failures.
Error codes and exact messages are not compared. The final fixed scalar/storage
regression passes 1,121 cases plus six matching errors and integrity checks.

All 207 executable tests, the full 274-job build, 1,066 registered headline
proofs, verification audit and live-path audit pass. The reverse-file matrix
passes 61 accepted cases and two declared unsupported shapes. New component
lemmas cover NULL propagation, copying the suffix after a source NUL and BLOB
quotation's equivalence to QUOTE. Near-gigabyte allocation behavior is not
empirically tested. Native code and its nine-binding audit boundary remain
unchanged. Reports use `sqlite-unicode-escape-*20261024.json` under
`docs/validation/`; these are bounded function results, not full SQL equivalence.


## LIKELY, UNLIKELY and LIKELIHOOD (2026-10-24)

Probability hints now validate and evaluate through the production scalar path.
LIKELIHOOD requires a REAL literal from 0.0 through 1.0 as its second argument,
as resolve.c:exprProbability does. INTEGER literals, unary operators, COLLATE,
computed constants and out-of-range values are preparation errors, including
on empty input and LIMIT zero. DISTINCT on these scalar calls remains inert.

The returned value retains its storage class and bytes. The function expression
has no comparison affinity: for example, wrapping a TEXT column in LIKELY does
not retain the column's automatic text coercion of a numeric comparison operand.
The hint also does not acquire its operand's static truth flag. Thus SELECT
likely(0) AND abs(Int64.min) still errors, while likely(0 AND abs(Int64.min))
returns zero. WHERE planning exposes hints and COLLATE wrappers for conditional
short-circuiting. The initial generalization of this behavior to HAVING was too
broad: the subsequent FILTER checkpoint below records the counterexample and
corrects HAVING's direct branch evaluation. The original bounded corpus did not
exercise that nested-NULL case. The probability value is not currently used for
a planner cost optimization.

The preceding source e0c2cb3cdb827fa3e3860604d890a7c0fd6cc46e01792485a47a7d353124145a
has 456 differences in 1,028 baseline outcomes, seed 353870. Development seed
353871 passes 1,508 outcomes. Final source is
`bdc24caa9646724af348c6c3e5067b1c9f90cb8a77423c899d621a59e241d5b3`.
Fresh seed 353872 passes **2,920 outcomes**, including **1,700 matching positive
error statuses**. Fresh WHERE/alias seed 353873 passes **1,248 outcomes**, including
636 matching errors. Both modes preserve main/WAL bytes for these reads. Success
compares exact CLI bytes; exact SQLite error codes/messages are not compared.
The fixed scalar/storage regression passes 1,121 cases plus six matching errors.

All 208 executable tests, the complete 276-job build, 1,068 registered headline
proofs, verification audit and live-path audit pass. The reverse-file matrix
passes 61 accepted cases and two declared unsupported shapes. Component lemmas
cover operand selection for a normalized LIKELY call and INTEGER probability
rejection; they are not a complete SQLite evaluator proof. Native code and its
nine-binding audit boundary remain unchanged. Reports use
`sqlite-probability-*20261024.json` under `docs/validation/`.


## Ordinary aggregate FILTER and predicate contexts (2026-10-24)

FILTER (WHERE expression) now works with the supported ordinary aggregates,
including DISTINCT, string separators, grouping, HAVING and outer ORDER BY.
The parser retains the clause in an internal expression wrapper; the independent
token grammar requires the corresponding FILTER syntax. A user function call
with the internal name cannot forge that syntax. Aggregate arguments and filter
names/functions validate before LIMIT/empty-input shortcuts. At execution the
filter runs before argument evaluation and before DISTINCT admission.

FILTER predicates do not contribute the aggregate result's collation metadata.
The new argument-selection map lemma preserves the existing name-binding and
read-collation refinement proofs. MIN/MAX identity includes its filter expression.
Retained source rows model SQLite's first-visit flag: grouped scans reset the
filtered-extremum control flag on each visit; ungrouped scans do so only when
there is no unfiltered extremum to initialize the source row. This distinction
is observable when filtered and unfiltered extrema appear together.

Development found a counterexample to the preceding probability-hint checkpoint's
HAVING generalization. WHERE planning exposes a hinted/collated condition, but
HAVING and FILTER branch on the wrapper and evaluate its operand as a scalar.
For example, likely(NULL AND abs(Int64.min)) skips the error as a WHERE condition,
but errors in an ungrouped HAVING or FILTER. Grouped HAVING may move a constant
condition into WHERE and skip the error again. These contexts now select the
corresponding evaluation rule; complete negative outcomes remain in the reports.

Baseline seed 353880 at source
bdc24caa9646724af348c6c3e5067b1c9f90cb8a77423c899d621a59e241d5b3
records 1,088 differences in 1,532 outcomes. The first development source
441ccd2f60f778c3deb1fb37ce6d8f7c975a7fb4de8b039a6b47b2b0a266b956
has two differences in 2,212 outcomes (353881), and ten in the expanded
1,596-outcome predicate-context corpus (353882). Corrected development seed
353883 passes 2,344 outcomes. Final source is
`271773dd04341eb1a63b13963ba8d940f96174fb0c8aa51f7f11ef76a8a8e594`.
Fresh seed 353884 passes **4,244 outcomes**, including **1,544 matching positive
error statuses**. Fresh HAVING regression 353885 passes **1,918 outcomes**, with
272 matching errors; probability regression 353886 passes **1,920 outcomes**,
with 1,120 matching errors. Both file modes compare exact CLI bytes or positive
error status and require unchanged main/WAL bytes on reads. Exact error codes
and messages are not compared.

All 209 executable tests, the full 276-job build, 1,070 registered headline
proofs, verification audit and live-path audit pass. The reverse-file matrix
passes 61 accepted cases and two declared unsupported shapes. Component proofs
cover unchanged rows without a filter and collation-argument mapping under a
syntax transformation. These do not establish complete SQL equivalence. Internal
aggregate ORDER BY and window clauses remain separate work. Native code and
its nine-binding audit boundary are unchanged. Reports use
`sqlite-aggregate-filter-*20261024.json` under `docs/validation/`.


## Aggregate-internal ORDER BY (2026-10-24)

Supported ordinary aggregates now accept ORDER BY inside their argument list,
including direction, explicit NULL placement, collations and FILTER. Internal
ordering expressions bind to input columns; integer expressions are values, not
output-column ordinals. The independent token grammar checks encoded order terms,
function argument limits and the separate 2,000-term ORDER BY limit. Zero-argument
function ordering is discarded before binding, matching SQLite, including
count(ORDER BY missing) and char(ORDER BY missing).

The accumulator input sorter evaluates keys even for DISTINCT duplicates.
Ordinary DISTINCT retains the first input before sorting. When the single
argument and single ordering expression are structurally identical, SQLite's
unique sorting-index optimization retains the last equal representative instead;
this includes equal INTEGER/REAL values and collated TEXT. MIN/MAX ignores its
ordering at execution but retains it in aggregate identity. Explicit default
NULL placement compares as the same ordering flags during aggregate sharing.

Ignored MIN/MAX ordering still resolves names and scalar function arities, but
emits no value or collation operations. Therefore unknown names/functions and
nested aggregates fail, while unused invalid collations, oversized hex literals
and runtime arithmetic errors do not. The pinned builtin registry supplies
167 preparation signatures (134 scalar entries); its complete metadata and
source fingerprint are retained in sqlite-builtin-signatures-20261024.json.
This is a static Lean signature table, excludes shell/application extensions,
and does not implement or delegate evaluation of those other functions. Deferred
hex literal spellings also remain invalid as LIKELIHOOD probability literals.

At source 271773dd04341eb1a63b13963ba8d940f96174fb0c8aa51f7f11ef76a8a8e594,
baseline 353890 has 1,048 differences in 1,232 outcomes. Development 353891
has eight ignored-collation differences in 1,772 outcomes; expanded development
353892 has eight ignored-literal differences in 2,044 outcomes. Both negative
reports remain. Corrected development 353893 passes 2,032 outcomes. Final source:
`88ac8e03532de20269e94efe192c1bdce471431dfaaeffc28684446ff29152f4`.
Fresh 353894 passes **3,632 outcomes**, including **1,054 matching positive error
statuses**. Fresh FILTER regression 353895 passes **2,444 outcomes** (790 matching
errors), and probability regression 353896 passes **1,720 outcomes** (1,006
matching errors). Both file modes compare exact CLI bytes and preserve main/WAL
bytes. Hex projections include malformed UTF-8 and embedded-NUL results. The
1,001/2,000/2,001 ordering-term boundaries are exercised. Error codes and wording
are not compared.

All 210 executable tests, the full 280-job build, 1,073 registered headline
proofs, verification audit and live-path audit pass. The reverse-file matrix
passes 61 accepted cases and two declared unsupported shapes. New component
lemmas cover order-term encoding/decoding, empty ordering identity and exact
signature arity. The sorter materializes inputs; no performance/scaling claim
is made. Window execution and broader SQL coverage remain incomplete. Native
code and its nine-binding audit boundary are unchanged. Reports use
`sqlite-aggregate-internal-order-*20261024.json` under `docs/validation/`.

## Mathematical scalar functions (2026-10-24)

The public scalar path implements the pinned ENABLE_MATH_FUNCTIONS registry:
29 names and 30 arities, including integer-preserving ceil/ceiling/floor/trunc,
trigonometric and hyperbolic functions, powers, logarithms, square root, radians,
degrees, pi and floating-point mod. Function preparation validates arity and
names independently of whether the expression executes.

The numeric-type conversion preserves REAL inputs and floating-point TEXT
spelling, rejects BLOB and malformed numeric text, and handles embedded NULs
like sqlite3_value_numeric_type. The two-argument log follows the actual pinned
func.c behavior: bases at or below one are rejected and the second argument
uses the permissive double conversion, including numeric prefixes and BLOBs.
NaN results become NULL; valid infinities and signed zeros are preserved.

Rounding clears binary64 fraction bits and adjusts the magnitude when required.
MOD aligns the exact dyadic significands, computes a Nat remainder and rescales
it by an exact power of two, covering subnormal values without a quotient-rounding
approximation. Transcendentals use Lean's existing standard-library Float/libm
operations. This introduces no project-native binding or SQLite delegation, but
those opaque standard-library functions are not formally verified here. Matching
on the tested host does not establish bit equivalence across all libm platforms.

Baseline seed 353900 at source 88ac8e03532de20269e94efe192c1bdce471431dfaaeffc28684446ff29152f4
records 5,668 differences, including two failed bulk writes, across 5,778 read
queries. Development 353901 passes 6,138 read outcomes and 5,922 stored values.
Final source is
`6f1fb1df2ecfa1e81c2cc24582b62919108cd9a4f6633ada9ebc789a3267f919`.
Fresh seed 353902 passes **10,538 read outcomes**, including **112 matching
positive error statuses**, and **10,322 stored values**. The expanded corpus
includes random finite binary64 bit patterns for rounding and MOD, moderate
and wide-exponent transcendental inputs, domain boundaries and storage types.
Both file modes compare exact CLI bytes and preserve main/WAL bytes on reads.
Stored results compare storage class, binary64 bits and raw bytes, with successful
integrity checks, using Python SQLite 3.45.1 only as the independent file observer;
the result oracle remains the pinned SQLite 3.53.4 CLI. The fresh bulk phase uses
an explicit transaction; the earlier development phase used individual commits.
Exact error codes/messages and exhaustive input coverage are not claimed.

The existing scalar regression passes 1,121 stored expressions and six error
cases. All 211 executable tests, the 282-job build, 1,076 registered headline
proofs, verification audit and live-path audit pass. Reverse-file validation
passes 61 accepted cells and two declared unsupported shapes. New component
proofs cover numeric INTEGER preservation, rounding INTEGER preservation and
NULL unary results, not complete numerical equivalence. The nine project-native
bindings and their audit list remain unchanged. Evidence uses
`sqlite-math-*20261024.json` under `docs/validation/`.

## SQL format / printf (2026-10-24–25)

FORMAT and PRINTF now execute on the public scalar path with SQL argument-stream
semantics, including zero arguments, missing arguments, ignored %n, %% and early
termination on unknown/internal conversion codes. An empty format or a leading
unknown conversion yields NULL; a successfully processed empty field yields
empty TEXT. The parser follows pinned flag precedence, 32-bit width/precision
wrapping, signed star arguments, and ignored l/ll length modifiers.

Integer formatting includes signed/unsigned 64-bit conversion, octal/hexadecimal,
uppercase pointer notation, ordinal suffixes, prefixes, precision, zero padding
and decimal separators. Strings retain arbitrary bytes, stop input at NUL, and
support byte or UTF-8-span precision and continuation-byte width accounting.
%c retains its SQL first-character/repetition semantics, including embedded NUL.
%q/%Q/%w quoting and %#q/%#Q control-code escapes follow the pinned source;
notably NULL %q/%w inputs produce (NULL) in 3.53.4. Floating formats use a general
port of sqlite3FpDecode with the existing integer power tables and 17-digit
round-trip shortening, 16/20 significant-digit limits, alternate forms,
zero/infinity rules, exponential selection and width/precision handling. No host
printf or new native binding is used. Output and temporary allocation sizes are
checked before constructing padding or repeated text. The actual 1 GB boundary
and allocation failure behavior have not been exhaustively exercised.

Baseline 353910 at source 6f1fb1df2ecfa1e81c2cc24582b62919108cd9a4f6633ada9ebc789a3267f919
records 4,086 differences, including two failed bulk writes, across 4,102 read
outcomes. Development 353911 passes 4,542 reads and 4,512 stored values. Final
source is
`8dcc714019b29c141cdd9966e5c0ce2920390ab799b652260c67e5e767e4586b`.
Fresh 353912 passes **7,418 read outcomes**, including **18 matching positive
error statuses**, and **7,388 stored values**. This includes a new generated
format-grammar corpus and explicit floating rounding boundaries. Both file modes
compare storage types and exact hex/CLI output, require unchanged main/WAL bytes
on reads, and compare persisted storage classes and raw bytes with integrity
checks. Python SQLite 3.45.1 is only the file observer; the result oracle is the
pinned SQLite 3.53.4 CLI. This is bounded behavior evidence, not exhaustive printf
or full SQL equivalence. Error codes and messages are not compared.

The existing scalar regression passes 1,121 expressions and six error cases.
All 212 executable tests, the 284-job build, 1,079 registered headline proofs,
verification audit and live-path audit pass. Reverse-file validation passes
61 accepted cells and two declared unsupported shapes. Component proofs cover
zero arguments, NULL format input and %n's unchanged argument stream. The nine
project-native bindings and their audit list are unchanged. Reports use
`sqlite-format-*20261024.json` under `docs/validation/`.

## Multi-page schema reads (2026-10-25)

The general file/WAL reader now traverses sqlite_schema as an ordinary table
B-tree rooted at page one. It accounts for the 100-byte database header on the
root, follows interior child pointers in order, and resolves schema-record
payload overflow through the existing bounded table-payload reader. A global
page budget, visited-page tracking and pointer bounds reject cycles, duplicate
children, out-of-file references and cells pointing into the B-tree header.
The logical table/index loading and validation after catalog decoding are
unchanged. This extends read compatibility; the proved bulk writer still
requires its schema entries to fit its single schema leaf.

At source 8dcc714019b29c141cdd9966e5c0ce2920390ab799b652260c67e5e767e4586b,
baseline 353920 records 169 differences in 177 read outcomes. Development
353921 passes 237 outcomes. Final source is
`3df3663e354335944dcd79bbe27974d414175c6a4aa40358aa8abea9854d9fb1`.
Fresh 353922 passes **307 outcomes**, comprising **297 successful exact-result
comparisons and ten matching positive corruption-error statuses**. Twenty
independently generated databases cover 512–65,536-byte page sizes, up to 451
tables, a schema tree with multiple interior pages, 70,000-character names,
schema overflow chains and committed WAL schema overlays. The pinned SQLite
3.53.4 dbstat topology, WAL frame counts and integrity checks are recorded.
The producer is closed before copies are opened; these are not concurrency
tests. All main/WAL bytes remain unchanged. Corruption checks include child
cycles, zero/out-of-file pointers, duplicate children and a header cell pointer;
exact error codes/messages are not compared.

All 213 executable tests, the 284-job build, 1,082 registered headline proofs,
verification audit and final live-path audit pass. Reverse-file validation
passes 61 accepted cells and two declared unsupported shapes. The first
live-path audit failed because it still searched for the replaced single-page
catalog call; the audit now checks the actual page-size-aware traversal and
existing table/index cell decoders. The negative audit log and check report are
preserved, and only that failed check was rerun. Unit regressions also exercise
schema entry order, invalid tree references and an overflow-chain cycle.
Component proofs cover an empty catalog record, completed traversal and an
exhausted budget; they do not prove complete SQLite file equivalence. Native
code and the nine-binding audit boundary are unchanged. Reports use
`sqlite-schema-pages-*20261025.*` under `docs/validation/`.

## Header page-count validity and physical tails (2026-10-25)

General opens and bulk pre-images now follow lockBtree/pagerPagecount: a nonzero
header page count is authoritative only when the change counter equals
version-valid-for. Otherwise the physical byte length, rounded up to whole
pages, supplies the count. A current count beyond physical EOF is rejected;
physical bytes/pages beyond a smaller current logical image are ignored.
A partial final base-file page is zero-filled, including when the WAL reader
falls back to a main-file page. This follows the ordinary SQLite VFS short-read
behavior. Reads retain original bytes, and bulk pre-images retain the actual
header bytes rather than silently rewriting stale size/counter fields.
Existing generated-image fast paths keep their stricter layout admission and
fall back to the general path when needed.

Baseline 353930 at source 3df3663e354335944dcd79bbe27974d414175c6a4aa40358aa8abea9854d9fb1
has 36 differing cases out of 48. Development 353931 passes 78 cases, including
an added partial empty-index-page fixture. Final source:
`b6d78537e72fc93ab1a3a00a652a3e0ea9ba7623bc776cfb3f8475eb784a43b7`.
Fresh 353932 passes **438 read cases**: **432 exact successful results and six
matching positive corruption errors**. All **432 applicable write cases** also
pass: UPDATE/INSERT results agree and pinned SQLite integrity_check returns ok.
The fresh corpus varies table contents, file sizes, stale 32-bit counters and
size fields, and uses 512-, 4,096- and 65,536-byte pages in both file modes.
It covers zero sizes, stale small/large sizes, trusted overlarge sizes, ignored
full/partial tails, and partial final empty pages. Input bytes remain unchanged
on reads. These are closed-file comparisons; concurrent locks and caches,
exact error diagnostics and arbitrary truncated-page behavior are not proved.

Fresh multi-page-schema regression 353933 passes 227 outcomes, including ten
matching corruption errors and committed WAL overlays. All 214 executable
tests, the 286-job build, 1,085 registered headline proofs, verification audit
and live-path audit pass. Reverse-file validation passes 61 accepted cells
and two declared unsupported shapes. Component proofs establish the zero,
stale-counter and current-counter branches of page-count selection. Native
code and its nine-binding audit list are unchanged. Reports use
`sqlite-header-size-*20261025.json` under `docs/validation/`.

## Reserved-byte page reads (2026-10-25)

Physical file offsets, page counts and WAL frame sizes now use the complete
page size. Table/index cells, schema pages and overflow chains receive only
the usable prefix, excluding the reserved tail. Header admission requires at
least 480 usable bytes. Fixed-4096 write caches decline reserved geometry.
The encoder still does not preserve extension-owned reserved bytes: rollback
writes, WAL writes and checkpoints reject these inputs before publication.
This is a read-compatibility improvement and explicit write limitation.

Baseline 353940 at source b6d78537e72fc93ab1a3a00a652a3e0ea9ba7623bc776cfb3f8475eb784a43b7
records 133 differences in 147 read cases. Development 353941 passes 189 cases.
Final source is `a803f1eb0d84ec584304df85dbfc3c90f91d1cb371670ff7bf8eead86d3e78db`.
Fresh 353942 passes **350 exact successful read comparisons** across 28
SQLite-created fixtures. Physical sizes range from 512 to 65,536 bytes; tails
include 1, 16, 32 and 255 bytes plus fresh randomized valid sizes. The fixtures
include table/index interior pages, payload overflow, and committed WAL
overlays after the producer closes. Reserved tails are filled with random
bytes, SQLite integrity_check succeeds, and Lean reads leave main/WAL bytes
unchanged. The independent oracle is the pinned SQLite 3.53.4 CLI.

Separately, **54 unsupported-write guard regressions** pass: UPDATE and WAL
checkpoint operations produce the stated unsupported diagnostic and leave
main/WAL contents unchanged. These refusals are not counted as compatible
SQLite writes. Native code and the nine-binding audit boundary are unchanged.
All 215 executable tests, the 286-job build, 1,086 registered headline proofs,
verification audit and live-path audit pass. The reverse-file suite passes
61 accepted cells and two declared unsupported shapes. Unit examples cover
physical/usable geometry, the 480-byte minimum and invalid sizes; the new
component theorem proves the exact usable-plus-reserved partition. Reports
use `sqlite-reserved-pages-*20261025.json` in `docs/validation/`.

## Database-header version admission (2026-10-25)

The public full-file and cold read paths now enforce the pinned SQLite read
version and schema-format checks. Read-version bytes greater than two reject
an image; future write-version bytes allow reads but reject write statements,
including statements inside transactions that would later roll back. Existing
IF NOT EXISTS schema no-ops remain successful. The version checks also guard
page-local writes, ordinary journal publication, page-size conversion and WAL
publication/checkpoint. As in sqlite3InitOne, schema-format admission uses the
low eight bits, with zero interpreted as the legacy format. The binary header
codec remains an exact codec rather than incorporating this execution policy.

WAL admission uses the latest committed page-one header, falling back to the
main header only when it has no overlay. An initial attempt to reject unknown
base-header versions before reading the WAL was incorrect: pagerOpenWalIfPresent
opens the WAL before B-tree header validation. The retained development report
records 42 failures in 150 cases from that attempt. The final implementation
removes that premature check and keeps the snapshot-specific validation.

Baseline 353950 at source a803f1eb0d84ec584304df85dbfc3c90f91d1cb371670ff7bf8eead86d3e78db
records 248 differences in 558 main-file cases. Main-file development 353951
passes 666 cases. Final source is `29f9ec7dcd2ee44485f8fc31f2fd109064d503c8b79eef90887b18310961f3a2`.
Fresh main-file seed 353952 passes **1,134 outcomes**, including 700
matching positive error statuses. Fresh WAL seed 353953 passes **450 outcomes**,
including 108 matching positive error statuses. Both corpus generators
vary row contents; main-file cases include SQLite-created and Lean-created
images, 512–65,536-byte pages, both file modes, zero/future format versions,
wrapped schema metadata, transactions, no-op writes and cold primary lookups.
WAL cases explicitly disagree between base and overlaid read/write/schema
versions, after producer shutdown, with recomputed frame checksums. Successful
writes compare persisted rows and require pinned SQLite integrity_check=ok;
reads and rejected operations retain original main/WAL bytes. Exact error
codes/messages and live concurrency remain separate work.

All 216 executable tests, the 288-job build, 1,089 registered headline proofs,
verification audit and final live-path audit pass. The first live-path audit
expected the old corrupt-header diagnostic; it now requires the new ordinary
'file is not a database' error and still rejects uncaught exceptions. Its
failure report/log are preserved; only that failed check was rerun. Reverse
validation passes 61 accepted cells and two declared unsupported shapes. The
three new component proofs cover unknown read versions, read-only write
versions and schema low-byte dependence. No native binding or audit-allowlist
change was made. Reports use `sqlite-header-version-*20261025.*`.

## DROP TABLE and DROP INDEX (2026-10-25)

The independent token grammar and public Core execution now accept DROP TABLE
and DROP INDEX, including IF EXISTS and existing single-token quoted-name
forms. Removing a table removes its owned indexes and retains other tables;
removing an explicit index retains the table's schema and rows. Primary-key
automatic indexes and the built-in schema tables remain protected. Missing
objects produce errors unless IF EXISTS applies. Logical changes use the
existing transaction snapshot, so ROLLBACK restores schema and rows together;
COMMIT and standalone statements use the ordinary file/WAL persistence path.
Missing-object no-ops skip publication. Qualified DROP names, views, triggers
and their dependencies remain outside this extension.

Baseline 353960 at source 29f9ec7dcd2ee44485f8fc31f2fd109064d503c8b79eef90887b18310961f3a2
records 156 differences in 210 outcomes. Development 353961 passes 210.
Final source is `9f8f4f169565a7e05419296c2045ad84d04447d5368fa4fb0984427e7d762b3b`.
Fresh seed 353962 passes **630 script outcomes**, including 198
matching positive errors. Separate read-only-format seed 353963 passes **210
outcomes**, including 186 matching positive errors. Each script uses
independent copies of a newly generated SQLite database with three tables,
ordinary/unique/automatic indexes and overflow data, at 512-, 4,096- and
65,536-byte page sizes, through both public file modes. After every script,
successful or failed, pinned SQLite compares the complete remaining object
names and row values and requires integrity_check=ok. This includes rollback,
commit, recreation and a second DROP failing after the first was persisted.
No SQL result filtering or diagnostic-oracle shortcut is used.

All 217 executable tests, the 290-job build, 1,094 registered headline proofs,
verification audit and live-path audit pass. The first full build found a
nonexistent test-only Except helper; the corrected second build passes.
Reverse validation passes 61 accepted cells and two declared unsupported
shapes. Component proofs state the retained table membership, unchanged rows
and schema after index removal, and exact schema no-op state. Native code and
its nine-binding audit list are unchanged. Reports use `sqlite-drop-*20261025.json`.

The retained broad SQL gap inventory was also rerun with --require-compatible;
it still exits nonzero. Its report, `sqlite-compatibility-gaps-after-drop-20261025.json`,
is a diagnostic inventory, not a coverage percentage or a claim of completion.

## INSERT SELECT (2026-10-25)

The public grammar and Core execution now support INSERT ... SELECT, including
INSERT OR ABORT, INSERT OR REPLACE and REPLACE ... SELECT over admitted SELECT
forms. The source is evaluated against the pre-statement database, then its
complete rows pass through the existing target-column mapping, affinity,
rowid and conflict-policy machinery. No SQL text is generated from result
values; the existing physical/scalar bridge retains storage classes and raw
TEXT bytes. Destination width and column names are validated even for empty
sources. The file engine recognizes INSERT SELECT as a write, including inside
transactions. OR IGNORE/FAIL/ROLLBACK and unsupported source-query forms remain
separate work.

Baseline 353970 at source 9f8f4f169565a7e05419296c2045ad84d04447d5368fa4fb0984427e7d762b3b
records 208 differences in 280 outcomes. Development 353971 initially records
eight differences in 368 outcomes: the pinned 3.53.4 shell continued to COMMIT
after a stepping error when all statements shared one input line. A separate
oracle protocol report reproduces this behavior and its absence with one
statement per line. The comparison now feeds both CLIs every statement on a
separate line, preserving quoted semicolons, and explicitly tests stopping at
the first error. The original negative report is retained; these eight cases
were not fixed by changing engine semantics or removed from the corpus.

Final source is `bdeaa889a933571d38664fd877a787e27e4963ad42bf45016144ebf48c5bb484`.
Fresh seed 353972 passes **1,184 script outcomes**, including 192 matching
positive error statuses. Newly generated source values and query combinations
cover exact stored bytes/types, TEXT/NUMERIC/REAL/BLOB destination behavior,
malformed UTF-8, NULs, duplicate target columns, source/destination overlap,
compound/grouped sources, ordering/offset/limit, empty results, unique-index
replacement and transaction rollback. All fixture tables are independently
read after every script, including failures, and pinned SQLite integrity_check
must return ok. Cases use 512-, 4,096- and 65,536-byte original files through
both public modes. Exact error diagnostics, shell one-line continuation and
unimplemented SELECT shapes are not claimed compatible by this suite.

All 218 executable tests, the 290-job build, 1,096 registered headline proofs,
verification audit and live-path audit pass. Reverse validation passes 61
accepted cells and two declared unsupported shapes. The new component proofs
cover an empty insertion sequence and the target-width admission branch; they
do not establish complete INSERT or SELECT equivalence. A development compile
failure in the new width theorem was corrected before evaluation. Native code
and the nine-binding audit boundary are unchanged. Reports use
`sqlite-insert-select-*20261025.json` under `docs/validation/`.

## VALUES queries and compound lowering (2026-10-25)

Production `VALUES` now executes through the checked Core grammar, including
multiple rows and compound SELECTs. First-row projection metadata is replayed
against the same source tokens as the actual first VALUES row; a forged AST
cannot replace the output expression behind an unchanged SQL spelling.
Single-row VALUES uses the ordinary scalar/aggregate constant SELECT path.
Multi-row VALUES validates each scalar row and keeps the 2,000-column bound;
unequal widths and ORDER BY/LIMIT after a final VALUES core are rejected.

`SQLite.Values` follows the constant-expression lowering in pinned
`insert.c:sqlite3MultiValues`: initial affinity-bearing rows remain separate
SELECTs, while a row without affinity starts a coroutine if another row follows.
This determines collation precedence, synthetic `columnN` binding, and which
OFFSET-skipped expressions are evaluated. Multi-row VALUES on the right of a
compound has the separate subquery-column metadata used by `parse.y`.
Compound binding uses the actual lowered projections; a coroutine does not
expose its defining expression as an outer ORDER BY expression. No query result
or reference output controls this decision. The direct-prefix length bound and
VALUES state preservation have kernel-checked component proofs; existing
translated-read claims retain their premises and conclusions.

Negative evidence is retained in `sqlite-values-query-negative-20261025.json`
(92 differences / 128 cases), `sqlite-values-query-development-20261025.json`
(4 / 168), and `sqlite-values-query-collation-negative-20261025.json` (2 / 520).
The last report exposed the CAST/collation lowering difference. The expanded
development run has 310 cases without differences. Final-checkpoint evaluation
uses fresh seed 353984 with 400 new generated queries: **1,030 public-file
executions, zero differences**, including 80 positive-error outcomes.
Both file modes are exercised. Successful reads compare exact output bytes and
retain main/WAL bytes; INSERT-from-VALUES compounds are reopened independently
with pinned SQLite for stored type/hex values and integrity. Error comparison
checks rejection, not exact error codes/messages or partial-output equivalence.
The fixed regressions include 1,001 rows and the 2,000/2,001-column boundary.

Implementation SHA-256: `9170396059a49e57e93cfd7884212ca70d246d65f5f4edaa7bd355425638c5c2`. The matching checks
report records a successful 292-job build, **219 executable tests**, the
verification and live-path audits, and 61 accepted reverse-file cells with two
explicitly unsupported cells. The nine native bindings are unchanged.
Reports: `docs/validation/sqlite-values-query-20261025.json` and
`docs/validation/sqlite-values-query-checks-20261025.json`; reproducible harness:
`scripts/run-values-query-differential.py`. This evidence covers the stated
VALUES forms, not CTEs, correlated subqueries, windows, or full SQLite equality.

## DELETE RETURNING old-row materialization (2026-10-25)

The production DELETE path now supports scalar `RETURNING` expressions and
unqualified `*` on admitted Core tables. `CoreReturning.prepare` binds the
original table name, expands visible columns, rejects qualified stars and
aggregates, and validates function calls before constant simplification, as
pinned `trigger.c:codeReturningTrigger` and `sqlite3ExpandReturning` do.
The DELETE alias remains available to WHERE but is not a RETURNING qualifier.
A result alias does not introduce a new input column. Ordinary rowid aliases,
implicit rowids, declared text primary keys and a visible column shadowing
`rowid` use the existing checked Core binding rules.

The ordinary expression DELETE planner selects rowid commands from the original
statement snapshot. RETURNING reads those old rows and computes the complete
output before running the Core commands. An expression failure therefore emits
no partial RETURNING output and cannot publish a prefix of the deletions. The
component theorem `CoreReturning.deletionOutput_length` proves one output row
per planned deletion on successful materialization. Existing DELETE statements
without RETURNING keep their existing execution and refinement proofs.

The retained baseline has **72 differences / 106 executions**. Development
seed 353991 has **360 executions / zero differences**. Final-checkpoint seed
353992 uses 100 new generated statements and three independently C-created
fixtures: **840 public-file executions, zero differences**, including
108 positive-error outcomes. Both file modes and page sizes 512, 4096 and
65536 are exercised, with transactions, explicit/implicit keys, an index,
NULLs, raw invalid-UTF-8 TEXT, embedded NULs and overflowing TEXT/BLOB payloads.
The pinned SQLite observer checks all remaining table rows with `typeof`/`hex`
and `integrity_check` after successes and errors. Failed individual statements
also retain the exact main/WAL bytes. Successful output comparison uses all
bytes; large passing captures are stored as lengths, SHA-256 and previews only
after comparison. Failures retain full captures. Error messages/codes and
partial output from preceding statements are not an equivalence claim here.

Implementation SHA-256: `14b4f2a548a59acc951a24946239c4b02cb55e21b4f6690aff75eaae5ef04b0a`. The matching check report
records a successful **294-job build, 220 executable tests**, both required
audits, and 61 accepted reverse-file cases with two declared unsupported cases.
Reports are `docs/validation/sqlite-delete-returning-20261025.json`,
`sqlite-delete-returning-checks-20261025.json`, and the retained negative and
development reports. Harness: `scripts/run-delete-returning-differential.py`.
INSERT/UPDATE RETURNING, RETURNING subqueries, triggers and virtual tables
remain separate work. These results do not establish whole-SQLite equivalence.

## INSERT OR IGNORE and discarded-input binding (2026-10-25)

INSERT OR IGNORE now handles the admitted Core schema's NOT NULL, rowid,
declared primary-key and explicit UNIQUE conflicts. Both VALUES and SELECT
sources use `CoreInsertIgnore.shouldInsert` followed by the ordinary checked
Core insertion. Constraint decisions use the current typed row and table,
not exception-message matching. Each accepted row changes the table before
checking the next; skipped rows retain the state and do not reserve a generated
rowid. INTEGER PRIMARY KEY datatype errors, expression failures and physical
value errors still fail the statement. The existing pure statement boundary
keeps an error from publishing an already processed prefix.

A generated development case exposed a pre-existing issue with repeated
INSERT target names: their discarded values were not bound. `rowValues` now
checks every input expression before selecting the first value assigned to a
repeated target. Thus an unused unknown column/function or invalid function
arity fails preparation, while an unused valid expression that would fail only
at runtime is not evaluated. Zero-AND binding follows the existing Scalar
preparation rules. This correction applies to ordinary INSERT as well.

Two kernel-checked component theorems establish that an admitted insertion has
no checked key conflict and that a skipped insertion preserves the exact Core
state with zero changes. Existing INSERT/REPLACE refinement statements retain
their premises and conclusions. No native binding was added or changed.

Retained baseline: **66 differences / 114 executions**. Development seed
354001: **16 differences / 364 executions**, all from discarded-input binding;
these failures remain in `sqlite-ignore-insert-development-20261025.json`.
Final-checkpoint seed 354002 uses 120 new generated INSERTs and fresh source
fixtures: **954 public-file executions, zero differences**, including 522
positive-error outcomes. The matrix includes page sizes 512/4096/65536, both
file modes, within-statement conflicts, NULL uniqueness, numeric affinity,
malformed TEXT, generated and signed-endpoint rowids, self-insertion, empty
SELECTs and transaction rollback/commit. All scripts are observed independently
with pinned SQLite for every table's type/hex values and integrity; rejected
single statements retain their main/WAL byte images. Error comparison checks
rejection, not exact messages/codes or partial outputs of preceding statements.

Implementation SHA-256: `6add864d465a4813212b8210640e354bb3c441b8ddd8ba588bab86ebf2893e2b`. The matching report
records a successful **296-job build, 221 executable tests**, both required
audits and 61 accepted reverse-file cells with two declared unsupported cells.
Reports: `docs/validation/sqlite-ignore-insert-20261025.json` and
`sqlite-ignore-insert-checks-20261025.json`; harness:
`scripts/run-ignore-insert-differential.py`. This checkpoint does not implement
UPDATE IGNORE, FAIL/ROLLBACK conflict policies, schema CHECK/foreign-key/default
constraints, nullable non-integer primary keys or the INT64_MAX random-rowid
fallback. It is not a claim of full SQLite compatibility.

## UPDATE OR IGNORE, key changes and index scan order (2026-10-25)

UPDATE OR IGNORE now evaluates assignments against each original input row
and checks the candidate against the state left by earlier accepted updates.
`CoreUpdateIgnore` privately removes the old row for the checked constraint
probe; a skipped candidate restores the exact preceding state and reports zero
changes. Accepted candidates use ordinary checked Core delete/insert commands.
INTEGER rowid NULL/type errors and expression failures still abort the entire
pure statement. The ordinary UPDATE fallback also permits changes to an
admitted declared text primary key. Repeated assignment binding, aliases,
transactions and simultaneous RHS evaluation retain their existing rules.

An ignored unique conflict makes traversal order observable. `CoreUpdateScan`
models the admitted single-column BINARY access terms and the default,
statistics-free SQLite costs, including covering access, IN multiplicity,
GLOB prefix bounds, NULL bounds and probability hints. `SQLite.PlannerCost`
ports the integer LogEst arithmetic and column/table/index size estimates.
Changing rowids or the selected scan column uses the rowid-collection order;
otherwise the selected index orders candidates. The sorting theorem proves a
permutation, not a complete optimizer equivalence theorem. STAT1/STAT4,
expression/partial/DESC/non-BINARY indexes and the full multi-index OR cost
search remain outside this implementation.

A fresh live-CREATE regression exposed inconsistent index order across opens.
`Table.addIndex` now appends to catalog creation order and both general index
decoders process catalog entries head first; the planner visits that list in
reverse. Canonical encoding/decoding retains the same list order. Four internal
CREATE INDEX contracts (`Table.addIndex_exact`, `execute_createIndex_exact`,
`CoreEndToEnd.WriteEffect`, `execute_createIndex_to_bytes`) explicitly change
the index-list conclusion from prepend to append. Their row/schema and frame
conditions are retained and the updated contracts are kernel checked. This is
an intentional representation-contract change, not an unchanged proof claim.

All counterexamples remain under `docs/validation/`: the initial UPDATE
baseline has 98 differences / 128 executions; the first development run has
16 / 388; the initial access-cost diagnostic has 48 / 90; the live-CREATE
index-order probe has 2 / 2. Intermediate passing single-index and cost
reports are retained with development-specific names. They are not substituted
for final-source evaluation. Development compile failures were corrected
before the final evaluation.

Final source SHA-256: `28953427b34b9c2139beeda0a4325f28636c839297bb26c26f7340185f1c0f11`.
Fresh seed 354016, 160 generated statements and three new C-created fixtures:
**1,194 executions, zero differences**, including 180 positive-error outcomes.
Fresh access diagnostic seed 354017: **90 executions, zero differences**.
Fresh creation-order seed 354018: **256 executions, zero differences**,
covering both file modes, live creation versus reopening, permutations of two
and three indexes, and dropping/recreating an index. The UPDATE fixtures use
512/4096/65536-byte pages. Each script is independently observed with pinned
SQLite for stored types/hex values and integrity. Failed individual statements
retain main/WAL bytes. Successful output is compared byte for byte; error
comparison checks rejection, not exact codes/messages or partial prior output.

The final check report records a successful **302-job build, 222 executable
tests, 1,105 headline component proofs**, both required audits, and 61 accepted
reverse-file cells with two declared unsupported cells. Native code and the
nine-binding audit boundary are unchanged. Reports:
`sqlite-ignore-update-20261025.json`, `sqlite-update-access-20261025.json`,
`sqlite-update-index-order-20261025.json`, and
`sqlite-ignore-update-checks-20261025.json`. Reproducible harnesses are
`scripts/run-ignore-update-differential.py`,
`scripts/probe-update-access-differential.py`, and
`scripts/probe-update-index-order-differential.py`. This evidence does not
establish full SQL, planner, database-format or WAL compatibility.


## UPDATE OR REPLACE with pending-row re-seeks (2026-10-25)

UPDATE OR REPLACE now freezes matching rowids before mutation, then re-seeks
each row in the state left by earlier replacements. A row removed by an earlier
unique-key replacement is skipped without evaluating its RHS. A row moved into
a later pending rowid is read again with its current values; for example, with
rowids 1/2/3, `SET id=id+1,v=v||'x'` can update the original first row three
times and leave rowid 4 with three appended characters. WHERE selection is not
re-evaluated against these changed values. This follows the non-one-pass path
in pinned `update.c`.

`CoreUpdateReplace.plan` validates the complete row using `Core.Row.create`,
then compiles deletion of the old row and all conflicting rowid/declared-key/
explicit-UNIQUE rows followed by one checked insertion. It never uses INSERT's
NULL-rowid allocation for UPDATE. NOT NULL violations without defaults and
ordinary evaluator/type errors abort the pure statement. Logical changes count
accepted updates, excluding replacement deletions. Three component proofs
cover candidate validation, exact pending-trace length, and unchanged-state
skipping of missing pending rows. They do not prove full SQLite equivalence.

Retained baseline seed 354020: **112 differences / 168 executions**.
Development seed 354021: **536 executions, zero differences**.
Final-checkpoint seed 354022 uses 160 new generated statements and three new
C-created fixtures: **1,284 executions, zero differences**, including 316
positive-error outcomes. Both file modes and 512/4096/65536-byte pages are
covered, with interacting unique keys, moved/deleted pending rows, text primary
keys, NULLs, malformed TEXT, repeated assignments, aliases, transactions and
signed rowid endpoints. Pinned SQLite independently checks every stored table's
type/hex values and integrity after each script. Rejected individual statements
retain main/WAL bytes. Error comparison checks rejection, not exact diagnostic
codes/messages or partial output from earlier statements.

Implementation SHA-256: `72373c344962205f573cd24f8994b5e4a770f790829ee70351ba4e482047348d`.
The matching checks report records a successful **304-job build, 223 executable
tests, 1,108 headline component proofs**, both audits and 61 accepted reverse-file
cells with two declared unsupported cells. A development proof-tactic failure
was corrected before evaluation. Native code and the nine host bindings are
unchanged. Reports: `sqlite-replace-update-negative-20261025.json`,
`sqlite-replace-update-development-20261025.json`,
`sqlite-replace-update-20261025.json`, and
`sqlite-replace-update-checks-20261025.json`; harness:
`scripts/run-replace-update-differential.py`. Schema defaults, triggers,
foreign keys, nullable non-integer primary keys and FAIL/ROLLBACK policies
remain separate work. These results are not a whole-SQLite percentage.


## INSERT RETURNING and INSERT-source grammar (2026-10-25)

INSERT VALUES, DEFAULT VALUES and admitted SELECT sources now support scalar
RETURNING expressions through the production Core path. `Statement.insert` and
`insertSelect` retain an optional RETURNING array, replayed against the input
SQL by `CoreTokenGrammar`. `CoreStatementForm` includes that new syntactic
field; the earlier no-RETURNING write-refinement statements retain their
premises and conclusions. The conformance-only Engine explicitly rejects the
new form; it is never used as a production fallback.

RETURNING binding uses the destination table's original name and visible
columns. Each accepted input row receives its generated rowid and write
affinity before ordinary checked Core commands run. Its RETURNING output is
then collected immediately, including when a later REPLACE deletes that row.
Ignored candidates retain the exact preceding state, allocate no rowid and do
not evaluate RETURNING expressions. A later expression or constraint error
aborts the complete pure statement and exposes no partial RETURNING output.
SELECT input is materialized from the pre-statement database, including
self-insertion. Component proofs establish unchanged-state/no-output IGNORE
and that output count cannot exceed input count. Result changes count accepted
rows. These are component guarantees, not full SQL equivalence proofs.

The parser now keeps RETURNING as a clause boundary after SELECT expressions
and sources. It accepts INSERT target aliases; in the admitted forms they are
not VALUES/RETURNING binding sources. UPSERT, where a target alias can have a
separate role, remains unsupported. A development refactor initially consumed
DEFAULT VALUES tokens too early; explicit monadic scoping corrected it before
final evaluation. Overlapping empty-array patterns were replaced by ordinary
branches to preserve Lean's generated equality theorems. Other development
compile failures were corrected without weakening the previous write proofs.

Retained baseline seed 354030: **76 differences / 166 executions**. Expanded
development seed 354031: **48 differences / 568 executions**, exposing the
DEFAULT VALUES, clause-boundary and alias gaps. The corrected development run
(seed 354032) has **568 executions, zero differences**. Final-checkpoint seed
354033 uses 160 new generated statements and three new C-created fixtures:
**1,332 executions, zero differences**, including 888 positive-error outcomes.
Both public file modes and 512/4096/65536-byte pages are exercised. Cases cover
IGNORE/REPLACE, simultaneous row conflicts, implicit/text/shadowed rowids,
malformed and embedded-NUL TEXT, overflowing BLOBs, 300-row insertion, the
2,000/2,001 RETURNING-column boundary, compounds, self-insertion and
transactions. Full successful output bytes and independently observed stored
type/hex values plus integrity are compared. Failed individual statements
retain main/WAL bytes. Error comparison checks rejection, not exact error
codes/messages or partial output from preceding statements.

Implementation SHA-256: `06970de9dfead129ebc6167606d28528d86772338866cc6e10c589b8235751de`.
The matching check report records a successful **304-job build, 224 executable
tests, 1,110 headline component proofs**, both required audits, and 61 accepted
reverse-file cells with two declared unsupported cells. Native code and its
nine-binding boundary are unchanged. Reports use
`sqlite-insert-returning-*20261025.json`; harness:
`scripts/run-insert-returning-differential.py`. UPDATE RETURNING, RETURNING
subqueries, UPSERT, triggers, virtual tables, schema defaults and full SQLite
compatibility remain separate work.


## UPDATE RETURNING with two-phase selection (2026-10-25)

UPDATE now retains and independently replays its RETURNING expressions. The
production path binds RHS/WHERE using the UPDATE alias and RETURNING using the
original target table name. As in pinned SQLite's RETURNING-trigger path,
matching rowids are collected before modification, even for IGNORE. Each
pending row is re-read from the current table, so earlier REPLACE deletions or
rowid moves affect later candidates. Accepted rows collect their new values
immediately; later replacements do not remove those output rows. A regression
with an indexed WHERE clause distinguishes this order from ordinary one-pass
UPDATE IGNORE, where a different row may win the same unique conflict.

All mutations use checked Core commands, with the existing typed IGNORE and
REPLACE helpers. Missing/ignored pending rows emit no output and do not evaluate
RETURNING expressions. Late expression or constraint errors discard the whole
statement. `CoreReturning.updatedOutput_zero`,
`CoreSQL.updateReturningRow_missing` and
`CoreSQL.updateReturningRows_length_le` prove these component skip/count
properties. No-RETURNING update-refinement statements keep their original
premises and conclusions. The syntax-form classification extends to the new
field. The conformance-only Engine explicitly rejects nonempty UPDATE
RETURNING; the public executable continues exclusively through Core.

Retained baseline seed 354040: **228 differences / 428 executions**.
Development seed 354041: **1,056 executions, zero differences**.
Final-checkpoint seed 354042 uses 160 new generated statements and three new
C-created fixtures: **2,082 executions, zero differences**, including 932
positive-error outcomes. Both file modes, 512/4096/65536-byte pages,
DEFAULT/ABORT/IGNORE/REPLACE behavior, interacting key changes, repeated
assignments, aliases, empty selections, transactions, type/hex output,
malformed and embedded-NUL TEXT, overflowing BLOBs and the 2,000/2,001 output
column boundary are exercised. Successful output bytes and independently
observed persisted types/hex values plus integrity are compared. Failed
individual statements retain main/WAL bytes. Exact error codes/messages and
partial output from preceding statements are not covered by that comparison.

Implementation SHA-256: `b4e9fe4a22a8717afe1669873a4c2c9cfdcca2e995f7795f5026e6e88e37368d`.
The matching checks report records a successful **304-job build, 225 executable
tests, 1,113 headline component proofs**, both required audits, and 61 accepted
reverse-file cells with two declared unsupported cells. Native code and its
nine-binding boundary are unchanged. Reports use
`sqlite-update-returning-*20261025.json`; harness:
`scripts/run-update-returning-differential.py`. RETURNING subqueries, triggers,
virtual tables, schema defaults, FAIL/ROLLBACK conflict behavior and full SQL/
database/WAL compatibility remain separate work.


## Scalar row-value UPDATE assignments (2026-10-25)

The parser now accepts grouped UPDATE targets such as `(v,u)=(u,v)`, mixed
scalar/grouped assignments, single-element target lists and extra parentheses
around scalar-expression rows. `SQLite.RowAssignment.bind` checks equal widths
before lowering to the existing ordered list of name/expression pairs. Its
component proofs establish the exact zip and retained target count. The
independent token matcher consumes each source target group against the same
consecutive AST pairs and replays their corresponding RHS expressions; it
cannot exchange or silently truncate them. A forged-RHS regression checks this
boundary. Subquery row assignments remain unsupported.

The existing assignment evaluator supplies simultaneous original-row reads,
affinity after expression evaluation, complete binding of discarded duplicate
assignments and last-target-wins behavior. All existing mutation/RETURNING paths
therefore handle the lowered form. Parser and token replay both enforce the
2,000-target SET-list limit, including the previously unbounded scalar form.
Two development parser type/scope failures were corrected before evaluation;
existing execution/refinement statements retain their premises and conclusions.

Retained baseline seed 354050: **80 differences / 124 executions**.
Development seed 354051: **448 executions, zero differences**.
Final-checkpoint seed 354052 uses 160 new generated statements and three new
C-created fixtures: **1,152 executions, zero differences**, including 378
positive-error outcomes. Both file modes and 512/4096/65536-byte pages are
covered, along with all admitted conflict policies, RETURNING, aliases, key
changes, duplicate targets, discarded runtime errors versus binding errors,
wrong widths even under WHERE 0, large BLOBs and the 2,000/2,001 assignment
boundary. Pinned SQLite independently checks persisted types/hex values and
integrity after each script. Successful output bytes are compared completely;
rejected individual statements retain main/WAL bytes. Exact diagnostic codes/
messages and partial output from earlier statements are not compared.

Implementation SHA-256: `256eb7e903869d5ad2511420fcc64d7694d1d56a07edd1ad7b1bda586515e4c8`.
The matching report records a successful **306-job build, 226 executable tests,
1,115 headline component proofs**, both required audits, and 61 accepted
reverse-file cells with two declared unsupported cells. The nine native
bindings are unchanged. Reports use `sqlite-update-tuples-*20261025.json`;
harness: `scripts/run-update-tuples-differential.py`. This is not a claim about
row-value comparisons, subqueries, all schema constraints or full SQLite
compatibility.


## Nullable TEXT keys and foreign pointer ordering (2026-10-25)

Ordinary TEXT PRIMARY KEY columns now retain their declared nullability.
SQLite's documented [PRIMARY KEY semantics](https://www.sqlite.org/lang_createtable.html#the_primary_key)
permit multiple NULL keys unless NOT NULL is explicit. The lookup cache uses
an INTEGER physical-rowid key for absent/NULL declared keys; admitted non-NULL
TEXT-affinity values are TEXT or BLOB, so the namespaces are disjoint. Record
and automatic-index payloads still contain the actual NULL. Component proofs
cover the NULL mapping, distinct-rowid injectivity and non-NULL preservation.

This deliberately extends `Schema.WellFormed` and canonical `Printable`:
only the physical INTEGER rowid alias must now be internally non-NULL.
The canonical printer/recognizer preserves explicit TEXT PRIMARY KEY NOT NULL,
and its inverse proof includes nullable TEXT keys. Previously generated bare
TEXT PRIMARY KEY declarations decode with their actual SQLite semantics; an
explicit NOT NULL declaration already lost in an older file cannot be inferred.

INSERT REPLACE and INSERT SELECT REPLACE now take the allocate-before-delete
trace for any declared non-rowid key, including when no explicit UNIQUE index
remains. The two ordinary `CoreSQLWriteText` REPLACE translation premises change
from `indexes.any unique = false` to `hasReplaceKeys = false`, matching this
route. Other Core replacement laws are not silently restated as SQL semantics.

The first expanded page-size evaluation exposed a separate decoder bug:
**94 differences / 2,808 executions**, all on a 4096-byte foreign fixture after
an independent C insertion of NULL. The first index pointer equalled the
content start but later pointers ran backwards. First-pointer coincidence was
insufficient to treat the payload as physically key-ordered. All four packed
page recognizers (catalog, table leaf, index leaf and index interior) now check
the whole pointer ordering. Foreign layouts failing the guard use the existing
pointer-directed decoder. The strengthened guard accepts generated pages by
proof; every existing generated-page inverse remains proved. The chunk-page
codec now reuses that common theorem. This guard is not claimed as a complete
corruption validator. Intermediate proof elaboration failures and the dependent
chunk-page proof were corrected before the final evaluation.

Retained SQL baselines: seed 354060 **166 / 318 differences**; expanded seed
354061 **170 / 294**. Initial development seed 354062 passed **576 executions**
but did not establish the missing cross-page property above. Both that result
and the later negative report are retained. Final seed 354064 regenerates the
initial payloads/unique values and 160 SQL statements: **3,528 executions,
zero differences**, including 1,098 positive-error outcomes. It crosses three
key-nullability states with 512/4096/65536-byte pages and both public file modes.
Each case compares successful output bytes, persisted types/hex values,
`table_info`, `index_list` and integrity, then checks an independent C write and
Lean reopen. Rejected individual statements retain main/WAL bytes. Seed 354065
adds **42 executions, zero differences** on C-mutated trees with 90–100 extra
rows, large keys, interior/overflow pages, updates, deletions and NULL insertion.
Exact diagnostics and partial output preceding a script error are not compared.

Implementation SHA-256: `0555378cab0bf120bb02b34aa8d2e6ef1ee2b3713059bd94834203e58cc3ddf4`.
The matching report records the successful **306-job build, 227 executable
tests, 1,120 headline component proofs**, both required audits, and 61 accepted
reverse-file cells with two declared unsupported cells. The nine native bindings
are unchanged. Reports use `sqlite-text-primary-*20261025.json`; harnesses are
`scripts/run-text-primary-differential.py` and
`scripts/run-pointer-layout-differential.py`. Composite keys, other declared
primary-key types, broader schema constraints and full SQL/database/WAL
compatibility remain unfinished.


## Single-column table PRIMARY KEY and INSERT rowid aliases (2026-10-25)

The live parser/checker/schema path now accepts single-column table PRIMARY
KEY declarations for the existing INTEGER and TEXT key types. Named constraints,
explicit ASC, BINARY collation and ON CONFLICT ABORT are admitted. INTEGER table
keys retain SQLite's rowid-alias behavior even with DESC or an index-only
collation name. TEXT descending/non-BINARY index forms remain unsupported.
`TableConstraintDef` now retains per-column collation and direction instead of
silently discarding them, including when reading a foreign schema. The checker
replays that exact metadata. Forged key targets, collations, directions and
conflict actions are rejected. Column order is preserved by `markPrimaryColumn`;
its size/name component laws and the no-table-constraint identity are registered.

The initial SQL differential also exposed an existing INSERT mapping error.
SQLite `insert.c` keeps the first input for ordinary repeated target columns,
but updates `ipkColumn` at every rowid/INTEGER PRIMARY KEY alias. `insertValueIndex`
now implements that distinction for named INSERT targets. For example, after
rows 1 and 2, `INSERT ... (rowid,k) VALUES(-10,NULL)` allocates row 3 when k is the
INTEGER alias. Reversing those names uses -10. Discarded single-VALUES expressions
are bound but not evaluated. INSERT SELECT already evaluates its source output.
Component laws record both first-ordinary and last-rowid selection. Existing
SQL-to-Core refinement statements retain their premises and conclusions, with
the corrected `rowValues` definition. Native code is unchanged.

Retained baseline seed 354070: **402 differences / 402 executions** (source
34eecfa8843a28181a7c20435d3ddf1a9dd3dfba501255a2f4125cd7d9db324b,
before the preceding pointer-order repair). Development seed 354071 found the
rowid-alias issue: **2 differences / 642 executions**. After correction, seed
354072 passed **924 executions**. Final seed 354073 regenerates initial data
and 120 SQL statements: **3,132 executions, zero differences**, including 1,258
positive-error outcomes. Both public file modes, all three 512/4096/65536-byte
page sizes, INTEGER/nullable TEXT/required TEXT keys and different key-column
positions are exercised. Successful output bytes, catalog object identities,
column/index metadata, persisted types/hex values and integrity are compared,
followed by independent C insertion and Lean reopen. Failed individual statements
retain main/WAL bytes; exact diagnostic text/codes and prior partial output are
not compared. Two test elaboration errors were fixed before final validation.

Implementation SHA-256: `8cd515d153dcac0c36a1e2971081be9e787617e107fa0d03a315d8f6901871cd`.
The matching report records a successful **306-job build, 228 executable tests,
1,125 headline component proofs**, both audits, and 61 accepted reverse-file
cells with two declared unsupported cells. Reports use
`sqlite-table-primary-*20261025.json`; harness:
`scripts/run-table-primary-differential.py`. Composite keys, schema conflict
defaults beyond ABORT, other key types and full compatibility remain unfinished.
A separate retained counterexample set for multiple-VALUES unused-expression
evaluation is the next task; this checkpoint does not claim that property.


## Complete multi-VALUES input evaluation (2026-10-25)

SQLite's multiple-VALUES source evaluates each complete input row before
selecting duplicate INSERT targets. A discarded ordinary-column or rowid-alias
expression can therefore raise an error, even if its row would later be ignored.
Single VALUES keeps its existing selective evaluation. `inputRowValues` now
carries this distinction through ordinary INSERT, IGNORE, REPLACE and RETURNING.
The mode is fixed from the original VALUES count and retained on every recursive
step, including the last row. INSERT SELECT already materializes source results
and keeps its existing path. Values cross the typed Core/Expr bridge without SQL
text rendering, preserving malformed TEXT, embedded NULs and BLOBs.

`evaluateInsertExpressions_evaluated` proves that successful materialization
has evaluated every source expression. `inputRowValues_single` proves the old
single-VALUES identity. The exact insert-command-trace theorem and RETURNING
count bound now quantify over the evaluation mode. Both `TranslatedInsertRows`
translation premises use `inputRowValues` with the original row count; the older
selectively evaluated premise would be insufficient and is not claimed unchanged.
Single-row refinements keep their contracts. A proof simplification was updated
to use the new identity lemma before evaluation.

Retained baseline seed 354080: **114 differences / 324 executions**.
Development seed 354081: **768 executions, zero differences**. Final seed 354082
regenerates initial payloads and 180 SQL statements: **1,248 executions, zero
differences**, including 954 positive-error outcomes. Both public file modes and
512/4096/65536-byte pages are exercised, with duplicate ordinary/rowid targets,
implicit and shadowed rowids, discarded first/last source errors, all admitted
conflict policies, RETURNING, SELECT sources, raw/embedded-NUL TEXT and overflowing
BLOB values. Successful output bytes and independently C-observed persisted
types/hex values plus integrity are compared. Rejected individual statements
retain main/WAL bytes. This measures success/error outcomes, not exact diagnostic
codes/messages or precedence among multiple independently invalid expressions.

Implementation SHA-256: `28ffe3ff15c53566d50e18a88ddfbc351a7d2157bf45416818b29ea03b0b6951`.
The matching report records the successful **306-job build, 229 executable tests,
1,127 headline component proofs**, both audits, and 61 accepted reverse-file
cells with two declared unsupported cells. Native code and its nine-binding
boundary are unchanged. Reports use `sqlite-insert-input-*20261025.json`;
harness: `scripts/run-insert-input-differential.py`. Schema defaults, stateful
functions, FAIL/ROLLBACK conflicts and full SQL/database/WAL compatibility remain
unfinished.


## Explicit INTEGER PRIMARY KEY NOT NULL metadata (2026-10-25)

`Core.Column.integerPrimaryNotNull` now records the explicit SQL declaration
separately from the existing internal `notNull` rowid invariant. A proof field
restricts the new marker to INTEGER rowid aliases. SQL schema admission sets it
from the original column declaration, including table-level primary keys. The
canonical printer emits the optional NOT NULL suffix and its recognizer restores
it; the inverse proof now covers both representations. The generic column
inverse retains its structural premises, while ranging over the richer column
representation. A registered component theorem covers the explicit suffix.
Older files whose declarations already lost this information cannot recover it.

NULL insertion still allocates a rowid with or without explicit NOT NULL, and
UPDATE to a NULL rowid still fails. Tests check both properties, different key
positions, column/table declarations and exact schema recovery after reopening.
The metadata distinction is visible to an independent C `PRAGMA table_info`;
it is not inferred from stored non-NULL data.

Retained baseline seed 354090: **70 differences / 180 executions**.
Development seed 354091: **540 executions, zero differences**. Final seed 354092
uses 18 newly populated fixtures and 60 new SQL statements: **2,520 executions,
zero differences**, including 576 positive-error outcomes. Both public file
modes, 512/4096/65536-byte pages, explicit/implicit NOT NULL, key-column positions,
all admitted conflict policies, RETURNING and transactions are covered. Output,
catalog/column/index metadata, persisted types/hex values and integrity are
compared, followed by independent C insertion and Lean reopen. Failed individual
statements retain main/WAL bytes. Diagnostic text/codes and partial output from
preceding statements are not compared. Two multiline record literals in the new
proof needed formatting corrections before final validation.

Implementation SHA-256: `1b287ddd367e18c54c526f21de6948ed454ae499e7da7b0da3213167d7e9da43`.
The matching report records a successful **306-job build, 230 executable tests,
1,128 headline component proofs**, both required audits, and 61 accepted
reverse-file cells with two declared unsupported cells. Native code and its
nine-binding boundary are unchanged. Reports use
`sqlite-integer-not-null-*20261025.json`; harness:
`scripts/run-integer-not-null-differential.py`. Other schema constraints,
case-preserving identifiers and full SQL/database/WAL compatibility remain
unfinished.

## Case-preserving SQL names (2026-10-25)

SQL binding now compares identifiers with ASCII case folding while retaining
original table, column and index names in the schema. `CoreNames` resolves the
SQL identifier to the exact stored object before Core commands execute; its
registered bridge proves that the resolved name retrieves that same table.
Core's exact-name database operations and frame invariants are unchanged.
SQL schema admission rejects case-insensitive duplicate columns and object-name
collisions, and DROP protects implicit primary indexes and reserved tables.
Actual columns still shadow rowid aliases. Non-ASCII letters remain distinct.

SELECT, joins, aggregates, compounds, all admitted writes, RETURNING and schema
no-ops use the resolved table name. Column/expression binding folds both sides.
The read/write text translation relations explicitly use `resolveTableName state`
in their lookup premises and target commands, rather than the old lowercased
name; CREATE INDEX's target retains the original index name. These translation
contracts have changed and are not claimed unchanged. The generated-file cold
read cache and wide insert path resolve names against their stored metadata.
Foreign canonical-shaped index SQL may spell its table/column differently;
the compatibility decoder resolves those references while retaining catalog
names and still checking physical index contents. The stricter generated-image
recognizer and its inverse proofs keep their existing exact-name contracts.

Retained baseline seed 354100: **168 differences / 192 paired scenarios**.
Development seed 354101: **366 scenarios, zero differences**. Final seed 354102
uses 120 new statements and newly populated fixtures: **2,718 scenarios, zero
differences**, including 126 positive-error outcomes. Both public file modes,
512/4096/65536-byte pages, quoted/escaped/spaced names, non-ASCII distinctions,
case variants, collisions, rowid shadowing, schema no-ops and transactions are
covered. Successful output bytes and independent C observations of catalog
names, column/index metadata, stored types/hex values and integrity are compared
without folding the observed names. Each case includes a subsequent C insert
and Lean reopen. Rejected individual statements retain main/WAL bytes. Original
DDL whitespace/SQL text, exact diagnostics and other SQL features are not covered
by this claim; names lost by earlier writers cannot be recovered.

Implementation SHA-256: `790df7e0b1bed85fc2709074b8e41c8077e1b9dba1c3c36fbe84c3ca400b8520`.
The matching checks record **308 build jobs, 231 executable tests, 1,131 headline
component proofs**, both audits and 61 accepted reverse-file cells with two
declared unsupported cells. The first full build hit a missing object at link
time when an incremental build was inadvertently started before it had fully
exited; the subsequent completed build and all evaluations use the final source.
Native code and its nine-binding boundary are unchanged. Reports:
`sqlite-schema-case-*20261025.json`; harness:
`scripts/run-schema-case-differential.py`. ALTER TABLE, broader schema constraints
and full SQL/database/WAL compatibility remain unfinished.

## Table and column renames (2026-10-25)

The production Core now executes `ALTER TABLE ... RENAME TO` and `RENAME
[COLUMN] ... TO` for its admitted schemas. Name lookup and collision checks use
ASCII case folding; new spellings are stored exactly. Renaming a table updates
its automatic TEXT-primary-key index name while retaining user index names.
Renaming a column retains index positions. Both operations retain row values
and physical rowids, including hidden rowids, NULL TEXT keys and rowid-shadowing
columns. Checked rebuilds retain all Core invariants. Four registered component
theorems describe column-count preservation and the exact schema/index/row or
database-table transformations. The public file engines mark both statements
as writes and retain transaction commit/rollback behavior. The text statement
form includes both operations; the unused legacy engine explicitly directs the
new table-rename form to the production Core instead of adding a fallback.

SQLite accepts empty table names. The extra nonempty-name clause was removed
from `Schema.WellFormed`; key, row-shape and unique-name conditions remain.
Dependent projections in the schema lookup and printer proofs were adjusted.
The printer/inverse already supports arbitrary identifier strings, including
empty strings and doubled quotes. Quoted names containing periods are now one
object-name token. Real schema qualifiers remain explicitly unsupported until
the AST separates them from literal periods; the checker no longer conflates
these two forms. CREATE/RENAME destination names and column declarations are
checked case-sensitively against tokens because their spelling is persistent
metadata. Executable tests reject forged casing in those declarations.

Retained baseline seed 354110: **180 differences / 228 scenarios**. The first
expanded run (seed 354111, **1,044 scenarios**) retained **36 output-order
differences** for two SELECTs without ORDER BY. All persisted metadata/data,
C follow-up writes and Lean reopens matched. SQLite used a covering index while
the Core used rowid order. These results remain in the unordered-negative report;
we do not claim identical optimizer choices or incidental scan order. The two
probes now request ORDER BY explicitly, consistent with SQLite's documented
undefined order when it is absent: https://sqlite.org/lang_select.html#orderby.
No result rows were sorted or filtered by the harness after execution.

Final seed 354112 regenerates 100 statements and fixture values:
**2,304 scenarios, zero differences**, including 144 positive-error outcomes.
Both public modes and 512/4096/65536-byte pages are covered, with quoted, empty,
escaped, dotted and non-ASCII names, collisions, case-only column renames,
rowid aliases/shadowing, transactions, malformed/NUL TEXT and overflowing table
and index payloads. Complete successful output bytes and C-observed catalog,
column/index metadata, typed persisted values and integrity are compared.
Every case includes a C schema write and Lean reopen. Failed single statements
retain main/WAL bytes. Large passing output captures are hashed only after the
full byte comparison; failing captures remain complete.

Implementation SHA-256: `b3a4b9b372bb2ac1637b9caa55b5efbc5c65e3a382a545f94b42457426613d29`.
The final checks record **310 build jobs, 232 executable tests, 1,135 headline
component proofs**, both audits and 61 accepted reverse-file cells with two
declared unsupported cells. Native code and its nine-binding boundary are
unchanged. Reports: `sqlite-schema-rename-*20261025.json`; harness:
`scripts/run-schema-rename-differential.py`. Dependent views/triggers/foreign
keys, original DDL text, qualified schemas and full SQL/database/WAL
compatibility remain outside this checkpoint.

## Empty index identifiers (2026-10-25)

A quoted empty index name is valid SQLite metadata. `Index.WellFormed` now
requires the column bound without the extra nonempty-name restriction. Index
list uniqueness and SQL's shared table/index namespace checks remain in force.
The generated-index decoding proof uses the retained bound directly; the new
registered `Index.wellFormed_rename` theorem makes name independence explicit.
The existing quoted printer, parser, lookup and DROP paths then handle the empty
name without a special execution path or schema-name substitution.

Retained baseline seed 354120: **132 differences / 132 scenarios**, including
files the Core previously could not open. Development seed 354121: **222
scenarios, zero differences**. Fresh seed 354122: **1,206 scenarios, zero
differences**, including 54 positive-error outcomes. Both public modes,
512/4096/65536-byte pages, long records/index payloads, schema collisions,
IF NOT EXISTS, UNIQUE enforcement, renames, DROP and transactions are checked.
C-observed names, column/index metadata, persisted type/hex values and integrity
are compared alongside successful output bytes; each case includes a C schema
write and Lean reopen. Failed individual statements retain main/WAL bytes.
Large passing captures are hashed only after complete byte comparison.

Implementation SHA-256: `9bda2570f586a4c46e311c5190c24fc7c8c2d2a4d3f59455a56df3d98607c880`.
The matching checks record **310 build jobs, 233 executable tests, 1,136 headline
component proofs**, both audits and 61 accepted reverse-file cells with two
declared unsupported cells. Native code and its nine-binding boundary are
unchanged. Reports: `sqlite-empty-index-*20261025.json`; harness:
`scripts/run-empty-index-differential.py`. This removes one identifier-domain
restriction; it is not a claim of full SQL/database/WAL compatibility.

## ADD COLUMN and omitted trailing fields (2026-10-25)

The production Core executes `ALTER TABLE ... ADD [COLUMN]` for ordinary
columns without a DEFAULT. The new visible field is inserted before a hidden
rowid, if present. Physical/declared key positions, the absent-key sentinel and
index positions shift consistently, while existing values and rowids are
retained. The new field initially contains NULL. NOT NULL additions to populated
tables fail; empty-table additions succeed. Case-insensitive duplicate names,
primary/unique additions, the 2,000-column bound and unsupported constraints are
checked before publication. Public write classification and transaction handling
include ADD COLUMN. Declared name/type/constraint tokens are checked by the
existing column recognizer.

SQLite can leave earlier records unchanged after adding columns. `CoreRecord`
now pads omitted trailing visible fields with NULL before decoding, then
reconstructs a hidden rowid separately. This is valid for the admitted schema,
which has no declared DEFAULT. Both byte-list and IO record readers use the same
function. `completeFields_record` proves padding leaves every valid generated
record unchanged; the original row/cell inverse theorem keeps its name and
premises through the exact decoder. Additional component theorems describe list
length, rowid retention and the exact checked table transformation. The first
component build exposed a missing minimum-bound simplification and a multiline
record formatting error; both were fixed before final evaluation.

Retained baseline seed 354130: **438 differences / 468 scenarios**. Development
seed 354131: **918 scenarios, zero differences**. Fresh seed 354132 regenerates
100 statements and fixture values, and rotates declared primary-key positions:
**2,178 scenarios, zero differences**, including 114 positive-error outcomes.
Both public modes, 512/4096/65536-byte pages, integer aliases, hidden rowids with
or without TEXT primary keys, empty/populated tables, quoted/empty/dotted names,
rowid shadowing, affinity, indexes and transactions are covered. Incoming C
fixtures include preexisting ADD COLUMN operations whose older records omit
fields, plus malformed/NUL TEXT and overflowing values. Each scenario includes
a subsequent C ADD COLUMN/update and Lean reopen. Full successful output bytes,
C-observed names/column/index metadata, stored types/hex values and integrity are
compared. Failed single statements retain main/WAL bytes. Large passing captures
are hashed only after their full comparisons.

Implementation SHA-256: `7deebde3064da20e4cd659091c4e596dc864288969afcf6974490c09f1346c78`.
The final checks record **312 build jobs, 234 executable tests, 1,141 headline
component proofs**, both audits and 61 accepted reverse-file cells with two
declared unsupported cells. Native code and its nine-binding boundary are
unchanged. Reports: `sqlite-schema-add-*20261025.json`; harness:
`scripts/run-schema-add-differential.py`. Declared defaults (including explicit
DEFAULT NULL), CHECK/generated/foreign-key additions, non-ABORT schema conflict
policies, DROP COLUMN and full SQL/database/WAL compatibility remain unfinished.

## DROP COLUMN (2026-10-25)

The production Core now executes `ALTER TABLE ... DROP [COLUMN]` for columns
in its admitted schemas. The checked operation refuses missing, last-visible,
rowid-alias, declared-primary-key and indexed columns. It removes only the
selected field from each schema/row, shifts later key/sentinel/index positions,
and retains rowids. Other columns retain their definitions and values. Registered
component theorems cover the size change, rowid retention, the required admission
guard and the exact successful schema/index/row transformation. The syntax,
checked grammar, text statement form and file-engine write classification all
include the new statement; the legacy engine remains outside production.

Retained baseline seed 354140: **417 differences / 648 scenarios**. Development
seed 354141: **918 scenarios, zero differences**. Fresh seed 354142 regenerates
100 statements and fixture values: **2,178 scenarios, zero differences**,
including 588 positive-error outcomes. Both public modes, 512/4096/65536-byte
pages, rotated column/key positions, integer aliases and hidden rowids with or
without TEXT keys, empty/populated tables, overflowing values, older records
with omitted trailing fields, rowid shadowing, quoted/empty/dotted names,
transaction rollback/commit and index removal before a column drop are checked.
Multi-statement cases also retain preceding successful schema changes when a
later statement fails. Each case includes a subsequent C ADD COLUMN and Lean
reopen. Successful output bytes, C-observed metadata, stored types/hex values
and integrity are compared; failed individual statements retain main/WAL bytes.
Large passing captures are hashed only after full comparisons.

Implementation SHA-256: `47972298ee143f6c39dce54485b13cf7558e6a7247af4eb8f052dcd3b5acc1ed`.
The final checks record **314 build jobs, 235 executable tests, 1,145 headline
component proofs**, both audits and 61 accepted reverse-file cells with two
declared unsupported cells. Native code and its nine-binding boundary are
unchanged. Reports: `sqlite-schema-drop-column-*20261025.json`; harness:
`scripts/run-schema-drop-column-differential.py`. CHECK/generated/foreign-key,
view/trigger dependencies and partial/expression indexes are not represented by
this Core schema, so this checkpoint does not cover their DROP restrictions.
Full SQL/database/WAL compatibility remains unfinished.


## Foreign catalog index admission and explicit ASC (2026-10-25)

Foreign index catalog SQL previously fell through to general SQL execution
when its spelling was not recognized by the canonical printer inverse. A
malformed entry could therefore execute UPDATE/DELETE or unrelated DDL during
an open; a valid noncanonical CREATE INDEX also skipped physical index-content
validation. The preserved baseline contains **184 cases / 120 differences**:
112/168 SQL comparisons and 8/16 separately labelled defensive integrity
probes. Setup initially failed because the pinned CLI enables defensive mode;
the harness disables it only on temporary fixture-building connections before
writable_schema modifications, never on production data or comparison readers.

`CoreSchemaSQL` now extracts only the first lexical statement, preserving its
original characters and stopping at a semicolon outside comments and quoted
values/identifiers. As SQLite 3.53.4 `prepare.c:sqlite3InitCallback` does, catalog
SQL must begin with CR before trimming, and the tail after the first statement
is ignored, including a malformed tail. The independent Core token grammar
replays this statement. Only a typed CREATE TABLE schema or a supported
single-column CREATE INDEX description can be returned; no statement executes.
Foreign CREATE TABLE fallback also uses this checked route, so a foreign key
cannot be silently discarded by the general parser. Unsupported constraints
remain explicit rejections, not implemented SQLite semantics.

Both index readers share `indexMetadata` and `checkedIndex`: catalog identity,
table/column binding, namespace and physical entries must agree. Every decoded
entry retains its physical rowid and position. The only value conversion is
SQLite's read-time REAL affinity, admitting integral REAL values stored with
INTEGER serial types; applying write affinity here would hide corrupt types.
NULL and empty automatic-index SQL both identify the implicit primary index.
The strict generated-image recognizer and its existing inverse theorems remain
unchanged. Explicit column PRIMARY KEY ASC and CREATE INDEX ASC now replay as
the default ascending order; DESC metadata remains unsupported.

New component contracts prove stopping at a lexical semicolon, preserving
index-entry rowids, identity of read conversion on already-admitted values,
and exact normalized contents as a necessary condition of checked admission.
Executable regressions exercise pure and IO paths, quoted semicolons, ignored
tails, wrong catalog identities/kinds, missing or reordered entries, incorrect
storage classes and foreign-key rejection. The live-path audit checks that
CoreDecode has no general SQL execution route and both readers use the check.

The expanded development run has **744 cases / 0 differences**. Final-checkpoint
fresh seed **354152** has **2,856 cases / 0 differences**: **2,808 SQL comparisons**
and **48 defensive integrity probes**. The latter require SQLite to diagnose
corruption and Lean to reject admission; they do not assert identical error
timing. Four affinities and page sizes 512/4096/65536 run in both public file
modes. Reads preserve main/WAL hashes. Valid explicit-index imports also undergo
Lean UPDATE, independent C integrity/data observation, C INSERT and Lean reopen.
The automatic-index empty-SQL case measures read admission. Complete output
bytes and positive error status are compared without result normalization.

Implementation SHA-256: `5bdbc2a28249b8ed01b2743a45716b83be32c1bcbeae99ef56ac23d5774abd8f`.
All **316 build jobs, 236 executable tests, 1,149 headline component proofs**,
both audits and the 61 accepted reverse-file cells pass; two reverse cells are
still declared unsupported. Intermediate builds exposed Lean proof-reduction
and syntax errors; the completed full build and final checks pass. Reports:
`sqlite-index-schema-*20261025.json`; harness:
`scripts/run-index-schema-differential.py`. Native bindings remain nine and
unchanged. This checkpoint does not establish full SQL/database/WAL equivalence.


## Live Core schema-inspection PRAGMAs (2026-10-25)

`PRAGMA table_info`, `table_xinfo`, `index_list`, `index_info` and `index_xinfo`
now read live Core metadata. No metadata cache is introduced. Table rows omit
the internal rowid column, retain declared names/type spelling, canonicalize
SQLite's six standard type names, and distinguish explicit INTEGER PRIMARY KEY
NOT NULL from the internal non-null rowid invariant. Primary-key ordinals and
implicit-index uniqueness/origin match the represented schema. Index lists use
reverse creation order; extended index info includes the auxiliary rowid with
cid -1, NULL name, BINARY collation and key=0. Built-in schema aliases expose
SQLite's five catalog columns. Missing objects or omitted arguments return no
rows for these five pragmas.

The operations are admitted by the independent token checker and exposed in
`CoreStatementForm`. A kernel-checked contract proves that successful execution
preserves the entire Core state; further contracts count visible-column and
index result rows. Tests inspect explicit/implicit keys, index order, declared
nullability, ALTER/DROP/CREATE changes, persistence round trips and rejection
of a forged operation/argument in token replay.

The initial negative run has **216/216 differences**. The first implementation
passed **1,098 development comparisons**, but an expanded grammar check found
**12/342 differences**: transparent expression parentheses had incorrectly been
accepted as PRAGMA arguments. That report is retained. The checker now consumes
a single admitted name token and rejects non-fallback keywords according to
SQLite 3.53.4 parse.y's nmnum rules, rather than replaying an arbitrary expression.
The expanded fixture initially attempted the same empty table and index name
in one SQL namespace; fixture setup failed, then these valid empty-name cases
were split across fixtures. No comparison result was manufactured from that
failed setup.

Final-checkpoint fresh seed **354164** has **2,826 comparisons / 0 differences**,
including **234 positive error cases**. It spans both public file modes,
512/4096/65536-byte pages, shifted primary-key column positions, empty names,
quoted periods/quotes, ASCII-only case binding, main/WAL read immutability and
subsequent C schema mutation followed by Lean re-query. Successful output bytes
and row order are compared verbatim; errors compare positive failure status,
not exact diagnostic text. The full **318 build jobs, 237 executable tests,
1,152 headline component proofs**, both audits and 61 accepted reverse-file
cells pass; two reverse-file cells remain declared unsupported. The initial
state-preservation proof required a helper-result refactoring; both completed
full builds pass and the final report uses the build after the grammar fix.

Implementation SHA-256: `a00cedbe35daf6a9754206fa652f84f19a8f316c0e688612a04bf7a0566c321d`.
Reports: `sqlite-schema-pragma-*20261025.json`; harness:
`scripts/run-schema-pragma-differential.py`. These are the five statement forms
over admitted Core schemas and the currently admitted name arguments. Numeric
PRAGMA arguments, explicit schema qualifiers, some bare keyword arguments,
table-valued PRAGMA functions and other PRAGMAs remain separate gaps. Native
code and its nine-binding boundary are unchanged. Full SQL/database/WAL
compatibility is still not established.


## PRAGMA atoms, preserved numeric names and explicit schemas (2026-10-25)

PRAGMA arguments now follow the dedicated nmnum grammar from SQLite 3.53.4
parse.y. They are a name or one numeric token with an optional sign, not a
SQL expression. Original numeric spelling is retained even for compact integer
values: 01, 1, 1.0 and 0x1 can identify different objects. Leading plus is
removed and minus is retained as pragma.c specifies. Digit separators remain
invalid in this grammar even though general SQLite numeric expressions allow
them. Bare fallback/contextual keywords are names here, so CAST, current_date,
ON and boolean words are not interpreted as expressions or executed functions.
The independent token replay checks both the numeric value and exact retained
spelling. Its control flow is separate from the parser; both use the explicit
pure token-classification and numeric-atom definitions in PragmaSyntax.

`Statement.pragma` now carries an optional schema name separately from the
operation name. This distinguishes main.table_info from the single quoted
unknown operation "main.table_info". main reads the persistent Core schema;
temp reads the currently empty temporary schema. Explicit main does not resolve
the temp-only catalog aliases. Unknown database names fail even for an unknown
pragma. Names absent from the pinned build's 66-name PRAGMA lookup table return
an empty result, as SQLite does. That recognition table is recorded from
pragma.h and the pinned build's pragma_list, not generated from comparison
outcomes. Known but unimplemented pragmas still fail explicitly; the table is
not a claim that all 66 operations are implemented. Temporary table creation
and attached databases remain unsupported.

The standalone state-preservation theorem now includes the explicit schema
argument. New component contracts preserve numeric spelling and show that a
qualifier whose lowercase resolution equals temp selects the empty schema.
The latter states the lowercase premise explicitly; an attempted concrete
String.toLower reduction did not kernel-reduce and is not claimed as a proved
normalization theorem. Unit regressions cover distinct numeric names, keyword
names, comments between sign and number, namespace separation, unknown-name
no-ops, invalid numeric expressions and forged spelling/schema certificates.
Legacy test-engine pattern matches were updated for the retained spelling and
new AST field; public execution remains on Core throughout.

The baseline is **1,548 comparisons / 432 differences**. The first development
run is retained as **1,698 comparisons / 12 differences**: JOIN and NOTHING
were missing from the forbidden bare-keyword set. Both were corrected. A
402-case metadata/reopen regression passed before this final keyword correction.
Final-checkpoint fresh seed **354172** has **4,236 comparisons / 0 differences**,
including **1164 positive error cases**, across six independent databases,
three page sizes and both public file modes. The suite includes every word in
the pinned keyword source, fixed numeric/quoted forms and fresh generated
numeric names; the first ten generated names also exist as tables, while the
remaining generated targets exercise misses and schema qualification. Every
read preserves main/WAL hashes. Full successful output bytes are compared;
error comparisons establish failure status, not exact error messages. The
fresh report records the reference PRAGMA list and compilation options.

Implementation SHA-256: `ae1f167e35184c0663cd3266cbfe52b73dddf8b3f21a6aca2c8fa3584f72cc7f`.
The final checks pass **320 build jobs, 238 executable tests, 1,154 headline
component proofs**, both audits and 61 accepted reverse-file cells; two reverse
cells remain declared unsupported. Reports: `sqlite-pragma-arguments-*20261025.json`;
harness: `scripts/run-pragma-arguments-differential.py`. Intermediate proof
failures and the negative keyword result led to the completed final build;
no failing result was relabelled as passing. Native code/bindings are unchanged.
Full SQL/database/WAL compatibility remains unfinished.

## CREATE TABLE AS SELECT / VALUES and exact expression names (2026-10-25)

CTAS now derives an unconstrained ordinary Core schema from the SELECT result,
then inserts its evaluated rows through the checked Core commands. Source
NOT NULL/PRIMARY KEY declarations and indexes are not copied. New rowids are
allocated in selection order. IF NOT EXISTS checks the shared object namespace
before binding or evaluating the source, and the existing transaction and file
publication boundaries include CTAS.

CoreCreateTableAs follows the pinned select.c/expr.c rules for inherited column
names, expression source names, boolean names, declared affinities and compound
result types. INTEGER/TEXT/NUMERIC/REAL affinities print INT/TEXT/NUM/REAL;
BLOB/no affinity has an empty type. COLLATE and likelihood wrappers affect name
inheritance separately from affinity. Case-insensitive duplicate names use the
SQLite colon-suffix rule. The later randomized suffix path remains explicitly
unsupported; this is not a claim to support every CTAS result shape.

The lexer now retains comments as whitespace tokens and re-escapes string
literal quotes when rendering tokens. The independent result-column replay
checks the exact consumed source text, so the AST cannot supply an arbitrary
CTAS column name. Nonempty block comments extending to end-of-input are accepted
as tokenize.c specifies; the exact two-byte /* remains an invalid expression.
Unit cases cover copied constraints, ordering/rowids, VALUES, duplicate names,
escaped/commented expressions, forged source text, rollback and codec inversion.
The two new component contracts cover fresh name allocation and the exact CTAS
Core command trace; they are not full SQLite-equivalence proofs.

Baseline seed 354180: **180 comparisons / 156 differences**. Development seed
354181: **300 / 6 differences**, all caused by the end-of-input block-comment
rule; this negative result is retained. After the fix, final-checkpoint fresh
seed **354182** has **2,340 comparisons / 0 differences**, including **72 positive
error cases**. Nine C-created fixtures cover page sizes 512/4096/65536, mixed-case
names, rotated column positions, nullable TEXT keys, older records after C ADD
COLUMN, long/overflow payloads and malformed TEXT. Both public file modes are
checked against pinned SQLite 3.53.4 using complete successful output and
independent C observations of catalog identities, column/index metadata,
typed values, rowids and integrity. C subsequently alters each database and
both engines reopen it. Explicit ORDER BY supplies ordering where CTAS rowid
assignment depends on source order. Errors compare failure status, not exact
messages. Original catalog SQL text is not compared; canonical rewriting is
still a separate compatibility limitation.

Implementation SHA-256: `b9698970fca6ece06386e71904fd1df9753a9aa7b176e8c30da65a5e0d071415`.
Final checks pass **322 build jobs, 239 executable tests, 1,156 headline component
proofs**, both audits and 61 accepted reverse-file cells; two reverse cells
remain declared unsupported. Reports: `sqlite-create-table-as-*20261025.json`;
harness: `scripts/run-create-table-as-differential.py`. Native code and the
nine-binding trust boundary are unchanged. Full SQL/database/WAL compatibility
is not established.

## Persisted NOT NULL conflict policies (2026-10-25)

Core columns now retain the schema's NOT NULL ABORT/IGNORE/REPLACE policy.
The representation requires a nondefault policy to belong to an explicit
NOT NULL declaration, including the separate explicit flag for INTEGER rowid
aliases. The canonical SQL printer/recognizer preserves the policy, with a
kernel-checked full schema inverse. The prior column inverse is retained as a
base recognizer lemma; the complete inverse composes it with policy recognition
and the new restoreNotNullConflict theorem. This also prevents an INTEGER
PRIMARY KEY ON CONFLICT clause from being mistaken for a NOT NULL policy.

Default INSERT/UPDATE checks NOT NULL columns in declaration order: an early
IGNORE skips the entire candidate before a later ABORT can fire. A skipped row
emits no RETURNING output. Rowid datatype errors and expression errors remain
errors. Without a DEFAULT value, NOT NULL REPLACE performs ABORT, as SQLite
specifies; DEFAULT values remain unsupported. Explicit statement OR actions
continue to override the schema policy. VALUES, INSERT SELECT, UPDATE,
RETURNING, schema rename and supported ADD COLUMN share the persisted metadata.
Repeated NOT NULL declarations now reset to ABORT when the last declaration
omits ON CONFLICT. Independent token replay reads each action and checks the
final policy, including rejecting an invented policy when SQL specifies none.

The existing single-command write/insert-trace relations now explicitly require
that a default-policy statement does not dispatch through active schema NULL
policies. This condition is unnecessary for explicit OR ABORT. The new skip
contracts establish unchanged state and zero changes for skipped candidates;
these component theorems do not establish complete SQLite SQL equivalence.
Schema FAIL/ROLLBACK and non-ABORT primary-key policies are explicitly rejected
instead of being silently discarded. Primary-key policy support is separate
follow-up work.

Baseline seed 354190: **432 comparisons / 232 differences**, retained. Development
seed 354191: **732 / 0**. After expanding the harness, final-checkpoint fresh seed
**354192** has **3,456 comparisons / 0 differences** across twelve C-created
fixtures and both public file modes. The expanded suite covers three page sizes,
INTEGER and nullable/NOT NULL TEXT keys, rowid allocation, mixed ordered NULL
policies, duplicate declarations, statement overrides, key/unique-index errors,
RETURNING evaluation, rollback, ADD/rename, overflow-sized and malformed TEXT.
C performs an additional NULL insertion into every resulting file before Lean
reopens it; failure status and independent C metadata/typed-row/integrity
observations verify that policies survive writes. Full successful outputs are
compared; error messages and original catalog SQL text are not compared. Failed
single statements preserve the Lean main/WAL byte hashes. The expanded harness
records actual fixture SQL, replacing unused case-flag annotations inherited
by the initial baseline/development harness.

Implementation SHA-256: `f38b419f1af57e28a1e033458ecf02873537530ce82037ac01559e79dee7a99b`.
Final checks pass **324 build jobs, 240 executable tests, 1,159 headline component
proofs**, both audits and 61 accepted reverse-file cells; two reverse cells remain
declared unsupported. The full build followed the resolved intermediate
component proof failures. Reports: `sqlite-schema-null-conflict-*20261025.json`;
harness: `scripts/run-schema-null-conflict-differential.py`. Native code and its
nine-binding boundary are unchanged. Full SQL/database/WAL compatibility remains
unfinished.

## Persisted PRIMARY KEY IGNORE / REPLACE policies (2026-10-25)

Column and single-column table PRIMARY KEY declarations now retain and execute
ABORT/IGNORE/REPLACE for the admitted INTEGER rowid aliases and TEXT keys.
Core.Column stores the policy with an invariant requiring an actual declared
key. Table-level lowering carries the action onto the target column while
preserving names/positions; its size/name proofs cover every action parameter.
The independent token replay also checks that an absent column ON CONFLICT
means ABORT, preventing a forged action from entering through an AST.

CoreDefaultConflict checks the actual typed candidate against the current
rows. Ordered NOT NULL checks precede uniqueness. A non-REPLACE rowid conflict
is handled before explicit unique indexes, whose default action is ABORT;
TEXT primary-key policies are checked after those indexes. REPLACE deletion is
deferred until checks that can skip or abort have completed. This order matters:
INTEGER PRIMARY KEY IGNORE can skip a row that also conflicts with an explicit
index, while TEXT PRIMARY KEY IGNORE does not suppress that index's ABORT.
REPLACE first allocates an insertion rowid against the original table, then
emits checked Core point deletions and one insertion. Explicit statement OR
actions retain their override behavior. Ordinary atomic errors discard the
statement; schema FAIL/ROLLBACK remain unsupported.

Default schema writes share this planner across VALUES, SELECT and RETURNING.
For UPDATE with a schema REPLACE policy, selected rowids are frozen and then
re-sought before each RHS evaluation. A prior replacement may delete a later
row or overwrite its pending rowid; stale values must not be reused. RETURNING
retains output already produced by an accepted candidate even if a later row
replaces it. SQL change counts count accepted candidates, excluding conflict
deletions. Component contracts cover the trace's final insertion and unchanged
state/output when a candidate is skipped; the old single-command relations now
exclude all active default schema-policy dispatch, not just NULL policies.

The canonical writer uses a quoted INTEGER/TEXT type and a trailing PRIMARY KEY
ON CONFLICT clause for nondefault key policies. This keeps explicit NOT NULL
and its policy independent of the rowid's internal non-NULL invariant. A plain
column recognizer is composed with key restoration, and the complete existing
schema inversion theorem remains kernel-checked for every admitted schema.
The intermediate base recognizer can end before a key constraint; complete
column/schema recognition still requires the actual constraint and separators.

Baseline seed 354200: **480 comparisons / 480 differences**. Development seed
354201: **780 / 0**. Final-checkpoint fresh seed **354202** has **3,576 comparisons
/ 0 differences**, including **974 positive error cases**. Twelve C-created
fixtures cover all three page sizes, column/table declarations, rotated column
positions, INTEGER/TEXT and nullable/NOT NULL keys, mixed schema/statement
policies, explicit unique indexes, repeated/duplicate INSERT targets,
RETURNING, pending UPDATE replacements, schema rename/ADD and long/overflow
keys and malformed TEXT. Complete successful outputs, error status and
independent C catalog/metadata/typed-row/integrity observations are compared.
C performs a further duplicate-key write before both engines reopen every file.
Single failing statements preserve Lean main/WAL hashes. Original schema SQL
text and exact error messages remain outside this measurement. A separate
final-source NULL-policy regression, seed **354195**, passes **888 / 0**.

An intermediate full check failed because the older table-key test still
expected IGNORE to be unsupported. That result is retained; the expectation
now tests still-unsupported FAIL, while new positive tests exercise IGNORE.
Inspection also found that the new NULL/key wiring checks had been appended
after the live-path script's terminal exit and were unreachable. They now run
before the exit and pass. The earlier NULL checkpoint's audit exit status was
accurately recorded as zero, but its newly appended wiring check did not run;
its independent unit, proof and differential results are unchanged. The final
checks explicitly rerun the corrected audit and tests. Unchanged verification
and reverse-file results are retained only after asserting the identical
production source hash.

Implementation SHA-256: `246eaeac593566ece6d002cb771877c534a9f9313a6e883dfb3988b1ff08d296`.
Final checks pass **326 build jobs, 241 executable tests, 1,163 headline component
proofs**, both audits and 61 accepted reverse-file cells; two reverse cells remain
declared unsupported. Reports: `sqlite-schema-primary-*20261025.json`; harness:
`scripts/run-schema-primary-conflict-differential.py`. Native code and its
nine-binding boundary are unchanged. These results do not establish complete
SQLite SQL/database/WAL equivalence.

## Persisted column DEFAULTs and staged preparation (2026-10-25)

The Core now retains checked DEFAULT SQL in column definitions. Omitted fields
and DEFAULT VALUES use the declared expression and column affinity; INTEGER
PRIMARY KEY omission still allocates a rowid without using its declared default.
Signed literals, identifier strings, booleans, blobs and the admitted closed
scalar expressions retain their spelling for PRAGMA table_info/table_xinfo.
One outer parenthesis pair is removed from the pragma span, as in SQLite.
Repeated DEFAULT clauses are independently checked and the last one is retained.

`ColumnDefault.Spec` contains SQL source and a proof that its independently
certified declaration is constant after the existing parser simplifications.
Function availability and runtime evaluation are separate stages: CREATE can
retain an unknown/wrong-arity function or a negated minimum hexadecimal value;
using the default later reports its preparation error. DEFAULT boolean code
elimination follows SQLite's code generation before function checks. Other
nonselected CASE branches still undergo preparation. Omitted constant defaults
are initialized even for an empty INSERT SELECT; replacement defaults undergo
preparation without running their runtime expressions. UPDATE prepares only
assigned columns. Stateful/date functions and subquery syntax remain incomplete.

NOT NULL REPLACE now substitutes the default with affinity. The first pass
continues through later constraints, so a later IGNORE can skip a row before a
second pass rejects a replacement that is still NULL. Explicit OR actions
override the schema policies. INSERT/UPDATE RETURNING projects the substituted
values. Checked Core row creation and command traces still enforce the actual
stored constraints; SQL change counts exclude replacement deletions.

ALTER ADD supplies literal/unary/CAST/boolean defaults to existing rows, using
the forms accepted by sqlite3ValueFromExpr. A nonconstant addition to a populated
table is rejected; an empty table can retain an expression without evaluating
it. Both physical record readers now complete short pre-ALTER records from the
column defaults. The hidden rowid is reconstructed independently. Missing-field
failures propagate rather than becoming NULL; full-width records retain their
existing proved decode/encode inverse.

Canonical schema SQL includes the ordinary DEFAULT expression and a comment
containing only the character lengths of the base column and default source.
The recognizer checks both pieces, their delimiters and the source certificate.
The comment contains no evaluated values or target semantics. The complete
schema inversion proof is extended to every admitted default-bearing column,
including arbitrary source text accepted by the certificate. The existing
NOT NULL and PRIMARY KEY policies round-trip independently. Original complete
sqlite_schema.sql text is still rewritten canonically, not preserved verbatim.

A further lexical counterexample showed that the old parser/checker treated
`X '80ff'` and `X/*gap*/'80ff'` as blobs. In SELECT these can instead be a column
and its string alias; as a DEFAULT they are invalid SQL. The parser and independent
literal checker now require an unquoted X token immediately adjacent to its
quote. This also prevents a malformed DEFAULT from entering a persisted schema.
Forged source, AST values, quoted prefixes and injected SQL are executable
negative regressions.

Preserved evidence:

- Baseline seed 354210: **400 comparisons / 346 differences**, on the preceding
  production source `246eaeac...`.
- Initial development seed 354211: **520 / 0**. Expanded preparation tests,
  seed 354212: **130 / 40**; empty-source/preparation tests, seed 354213:
  **214 / 18**. Both negative reports are retained with their actual source hashes.
- Before the blob fix, seed 354214 passed **4,968 / 0**, a key-policy regression
  passed **948 / 0**, and all checks passed. These reports are explicitly named
  `before-blob`; the separate blob corpus, seed 354216, found **240 / 48**.
- Final-source fresh seed **354217**: **4,968 / 0**, including **984**
  positive error cases. Twelve C-created fixtures cover 512/4096/65536-byte pages,
  both file modes, rotated columns, key/NULL policies, old short records,
  overflow TEXT, malformed TEXT, DEFAULT timing, affinities, RETURNING and ALTER.
- Final-source blob seed **354218**: **480 / 0**, including 224 positive error
  cases; key/NULL-policy regression seed **354219**: **948 / 0**, including 206
  positive error cases. Every final report records the same production hash.

Comparisons include complete successful output, error status and independent
C catalog/pragma/typed-row/integrity observations. C then inserts omitted fields
and Lean reopens the result. Single failing statements preserve main/WAL hashes.
The blob corpus separately checks persisted catalog and row observations. Exact
error messages/codes, live WAL concurrency, original catalog SQL and unsupported
SQL features are outside these metrics. The larger corpus was rerun with a fresh
seed after the final lexical fix; earlier green results were not relabeled.

Implementation SHA-256: `d4f19143c342f63ca097a4b91f5d0d0e6831e53debc41f8a1bb5fff0eb1e4508`.
Final checks pass **330 build jobs, 243 executable tests, 1,168 headline component
proofs**, both audits and 61 accepted reverse-file cells; two reverse cells remain
declared unsupported. The live-path audit's new DEFAULT checks run before its
terminal exit. Reports: `sqlite-column-default-*20261025.json`; harnesses:
`scripts/run-column-default-differential.py` and
`scripts/run-blob-token-differential.py`. Native code and its nine-binding
boundary are unchanged. These are scoped component/SQL/file results, not complete
SQLite SQL/database/WAL equivalence.

## Named column and table constraints (2026-10-25)

The certified grammar now accepts CONSTRAINT names on the admitted column
constraints: PRIMARY KEY, NOT NULL, NULL, DEFAULT and BINARY COLLATE. Names may
be quoted, empty, Unicode or permitted fallback keywords; reserved words and
numeric tokens require valid quoting. The parser and independent checker both
validate the name token instead of accepting every identifier-shaped keyword.
Constraint names do not alter these constraints' enforcement or conflict policy.

SQLite's table CONSTRAINT-name production can appear repeatedly, stand alone,
precede or follow a real constraint, and use optional intervening commas. The
parser now consumes repeated leading names; the independent table-constraint
loop handles standalone names and still matches each actual PRIMARY KEY against
exactly one retained AST constraint. Trailing/doubled commas and columns after
the table-constraint section remain rejected. A name-only production cannot
forge a primary key or hide an unimplemented constraint. Regressions exercise
that failure and reserved-name forgery directly against the token checker.

Foreign named schemas now load through the same Core schema translation, and
ADD/rename/write/reopen preserve the constraints' behavior. Canonical persistence
continues to omit these semantically unused names; complete original catalog SQL
is not preserved. Named CHECK, foreign-key and UNIQUE enforcement remain outside
the admitted surface because those constraints themselves are still incomplete.

Baseline seed 354220: **336 comparisons / 312 differences**. The expanded table
name and invalid-name corpus, seed 354221, records **166 / 136** on the same prior
production source. Development seed 354222 passes **618 / 0**. Final-checkpoint
fresh seed **354223** passes **4,392 / 0**, including **296** positive error
cases. Twelve C-created fixtures cover 512/4096/65536-byte pages, both file modes,
column/table keys, key/NULL conflict policies, rotated columns, quoted/repeated
names, ALTER, RETURNING, long and malformed TEXT. C checks catalog, typed rows,
pragmas and integrity, then writes again before Lean reopens. The final-source
DEFAULT regression, seed **354224**, passes **1,524 / 0**.

Implementation SHA-256: `951b6fe3f84823feefa8ffd4b2feee37b2349f2ec3e1a5cdd74375d2feb172e8`.
Final checks pass **330 build jobs, 244 executable tests, 1,168 headline component
proofs**, both audits and 61 accepted reverse-file cells; two reverse cells remain
declared unsupported. The existing certified-parse contracts cover the updated
checker; no new proof count is claimed. The live-path name-grammar check runs
before the terminal exit. Reports: `sqlite-named-column-constraint-*20261025.json`;
harness: `scripts/run-named-column-constraint-differential.py`. Native bindings
are unchanged. This is scoped grammar/SQL/file evidence, not complete SQLite
compatibility.

## Column type grammar, source spans and metadata (2026-10-25)

The parser and independent token checker now validate SQLite 3.53.4's
`typetoken`/`typename`/`signed` productions. Type dimensions contain one or two
signed numeric tokens; expression syntax, extra dimensions, misplaced numbers,
non-fallback words and numeric separators are rejected. An adjacent `X'...'`
blob token cannot serve as a type word. Spaced or comment-separated X and string
tokens remain ordinary type words. The type span ends at its final token, before
trailing comments. The checker requires the exact source spelling and internal
trivia, so a semantically similar token stream cannot forge the retained type.

Public metadata follows the pinned build.c implementation: the six standard
names normalize only when the complete adjusted span is one standard name;
custom quoted types dequote their first token, and ordinary multiword types keep
their original spelling. The historical trailing ALWAYS/GENERATED adjustment is
applied once, including its byte-length threshold and suffix-inside-word cases.
Internal comments left by this adjustment prevent standard-name recognition.
Lean's existing case conversions already fold ASCII only; no new Unicode folding
behavior is introduced.

An explicit empty type (`""`, `''` or `[]`) now retains NUMERIC affinity separately
from an absent type's BLOB affinity, although both display an empty pragma type.
Canonical SQL prints an explicit empty quoted type when required. It uses a
precision suffix for a custom lowercase standard-looking name, such as
`"text"(0)`, to keep C from changing its metadata to TEXT. These are ordinary SQL
type declarations. The general typed-column inverse now covers empty names and
case-preserving suffixes, and the complete schema/record codec proofs remain in
place. The explicit-empty affinity theorem is registered in the component audit.

INTEGER rowid-alias detection now uses the standard type classification instead
of comparing only the dequoted display name. A trailing comment no longer breaks
an actual alias. A custom type such as `"INTEGER" extra PRIMARY KEY` is correctly
recognized as a non-alias key, but its execution remains unsupported at this
checkpoint. The separately labelled key diagnostic preserves that gap, including
INT/REAL/NUMERIC/BLOB/untyped and custom lowercase TEXT keys. No passing type
metric includes those failures. Canonical rewriting of complete catalog SQL,
generated columns and live concurrent WAL coordination remain separate gaps.

Preserved baseline seed 354230: **552 comparisons / 300 differences**. Expanded
source-span baseline seed 354231: **212 / 124**. Development seed 354232:
**1,020 / 0**. The explicit non-alias key diagnostic, seed 354233, records
**18 / 18**, all with successful C execution and unsupported Lean execution.

Final-checkpoint fresh seed **354234** passes **6,000 / 0**, including
**1824** positive error cases. Twelve C-created fixtures cover
512/4096/65536-byte pages, both file modes, rotated key columns, key/NULL policies,
old records, overflow and malformed TEXT, empty/custom types and large numeric
parameters. Comparisons include complete successful output, error status,
independent C catalog/pragma/typed-row/integrity observations, a subsequent C write
and Lean reopen. Failing single statements preserve main/WAL hashes. Exact error
messages/codes, original catalog SQL and concurrent WAL locking are outside this
metric. DEFAULT regression seed **354235** passes **1,524 / 0**; named-constraint
regression seed **354236** passes **618 / 0**, on the same final production source.

Implementation SHA-256: `ef00424ddcd8be114d32175771d3dbc2fce31db540d710c660fcda932269437d`.
Final checks pass **332 build jobs, 245 executable tests, 1,169 headline component
proofs**, both audits and 61 accepted reverse-file cells; two reverse cells remain
declared unsupported. The new type/affinity live-path checks run before the
terminal exit. Reports: `sqlite-column-type-*20261025.json`; harness:
`scripts/run-column-type-differential.py`. Native code and the nine-binding audit
boundary are unchanged. These are scoped SQL/file/component results, not complete
SQLite compatibility.

## Indexed primary keys with arbitrary declared types (2026-10-25)

Single-column ascending BINARY primary keys now admit every supported declared
type, including INT, REAL, NUMERIC, BLOB, no type, an explicitly empty type and
custom quoted INTEGER/TEXT names. Exact standard INTEGER remains the rowid alias.
Other keys keep a separate rowid, their actual field value, a primary automatic
index, their declared metadata, and their own affinity. Column and table key
syntax, NULL/NOT NULL, admitted conflict policies and defaults share this path.
Composite, descending and non-BINARY key indexes remain separate work.

The old nullable-TEXT lookup cache represented NULL rows by INTEGER rowids. That
representation relied on TEXT-affinity values occupying other storage classes.
The new DeclaredKey type separates row identities from actual SQL keys, and a
registered theorem proves that every NULL key is distinct from every non-NULL
key, independently of numeric values. Existing balanced-map representation,
lookup, insert and update proofs are updated to the tagged key space.

The lookup key also canonicalizes exactly integral binary64 values to bounded
INTEGERs, including signed zero and INT64_MIN. Candidate integers are derived
from the binary significand/exponent and checked using the exact integer/binary64
comparator. Stored values retain their original storage class. A component
proof establishes that canonicalization preserves numeric comparison equality;
regressions cover the integer/real boundary around 2^53, INT64 bounds and
infinities. This does not assert a full formal equivalence proof for SQLite's
complete constraint engine.

Indexed type metadata has a separate, invariant-carrying Core representation.
Canonical SQL prints the actual type, NULL/NOT NULL policy and PRIMARY KEY policy.
A `(0)` suffix on quoted type names prevents an INTEGER display name from silently
becoming a rowid alias. A fixed comment identifies this syntax for the recognizer;
it carries no values, types or constraint policies. The recognizer validates the
entire ordinary SQL body, including the required suffix. The general key-column,
default-column and complete schema inverses cover the expanded representation.
C therefore sees the same constraints that the recognizer reconstructs.

Baseline seed 354240 records **468 comparisons / 420 differences**. Development
seed 354241 passes **612 / 0**; the expanded search/delete/default/NOT NULL corpus,
seed 354242, passes **900 / 0**. Reports keep each corpus and its actual source and
harness hashes. The first final-check audit run found one stale static rule that
still required the old INTEGER-valued NULL surrogate. Its failure is retained in
`sqlite-indexed-primary-checks-before-key-audit-20261025.json`. The rule now checks
the rowid constructor and additionally requires the NULL/non-NULL disjointness
proof. Other successful checks were retained; only the affected audit was rerun.

Final-checkpoint fresh seed **354243** passes **5,520 / 0**, including
**1992** positive error cases. Twelve C-created fixtures cover
512/4096/65536-byte pages, both file modes, C-created indexed-key tables, column
and table declarations, conflict policies, defaults, searches, updates, deletes,
RETURNING, overflow and malformed TEXT. Complete successful output, error status,
C catalog/pragma/typed-row/integrity observations, subsequent C writes and Lean
reopens are compared. The previous unsupported-key corpus passes **54 / 0** on
fresh seed 354246. Column-type regression seed **354244** passes **2,040 / 0**;
DEFAULT regression seed **354245** passes **1,524 / 0**. All final reports identify
the same production source.

Implementation SHA-256: `d77c9767b8ed0ddb216ba70455054d5edcce3a66e814a0bec802ecd3417d0f39`.
Final checks pass **334 build jobs, 246 executable tests, 1,173 headline component
proofs**, both audits and 61 accepted reverse-file cells; two reverse cells remain
declared unsupported. Reports: `sqlite-indexed-primary-*20261025.json`; harness:
`scripts/run-indexed-primary-differential.py`. The nine native bindings are
unchanged. Exact diagnostics, original complete catalog SQL, concurrent WAL
coordination and the remaining unimplemented SQL features are outside these
scoped SQL/file/component metrics.

## AUTOINCREMENT and sqlite_sequence (2026-10-25)

INTEGER PRIMARY KEY AUTOINCREMENT now retains a statement-local high-water mark
and the ordinary sqlite_sequence table. Allocation uses the larger of the current
table end and the saved counter; INT64_MAX fails instead of reusing an identifier.
Candidates skipped by IGNORE still advance the counter. Failed statements discard
it, and transaction rollback restores both rows and sequence history. UPDATE does
not advance the history. Empty successful INSERT SELECT creates a zero entry.
Sequence publication happens after source selection and RETURNING evaluation.

Existing sequence rows retain their storage class unless their integerized value
increases. Lookup uses the first exact TEXT name, including duplicate entries and
case distinctions. Explicit negative rowids, manually edited numeric/text/blob/
NULL counters, rename and drop follow the pinned C implementation. Rename also
updates manually inserted sequence entries belonging to ordinary tables; ordinary
table drop leaves those entries. Public DDL cannot alter/drop sqlite_sequence or
index an internal sqlite_ table.

Column and table AUTOINCREMENT syntax is independently replayed against tokens.
The canonical recognizer validates the complete ordinary SQL declaration, with
AUTOINCREMENT, default and conflict policies visible to C. Its general column and
schema inverse proofs include the new metadata. Counter allocation and monotonic
advancement have component proofs. The older one-command write-translation
relations now explicitly require non-AUTOINCREMENT schemas, since this feature
also writes the sequence table. Optimized one-table insert paths fall back to
complete publication for AUTOINCREMENT tables, preserving both modified tables.

Baseline seed 354250 records **252 comparisons / 228 differences**. The expanded
development corpus, seed 354251, records **498 / 18**: prohibited sequence indexes
were accepted, and ordinary-table rename missed manual sequence entries. Both
counterexamples remain in the reports and subsequent evaluation.

Final-checkpoint fresh seed **354252** passes **3,912 / 0**, including **432**
expected error cases. Twelve C-created fixtures cover 512/4096/65536-byte pages,
both file modes, imported AUTOINCREMENT history, ignored rows, RETURNING,
transaction rollback, schema changes, malformed TEXT and overflow in neighboring
tables. Complete successful output, error status, C catalog/pragma/typed-row/
integrity observations, subsequent C writes and Lean reopens are compared.
Indexed-primary regression seed **354253** passes **1,020 / 0**; DEFAULT regression
seed **354254** passes **882 / 0**, on the same final production source.

Implementation SHA-256: `4ba487488aaf236e07103795d6532937028e97634af23c8852f0dbe46892ca73`.
Final checks pass **336 build jobs, 247 executable tests, 1,178 headline component
proofs**, both audits and 61 accepted reverse-file cells; two reverse cells remain
declared unsupported. Reports: `sqlite-autoincrement-*20261025.json`; harness:
`scripts/run-autoincrement-differential.py`. Native code and the nine-binding audit
boundary are unchanged. These scoped results do not establish full SQLite
compatibility: concurrent WAL coordination, ordinary random rowid allocation at
INT64_MAX (including sqlite_sequence's own rowids), exact diagnostics and other
unimplemented SQL remain separate work.

## SAVEPOINT, RELEASE and ROLLBACK TO (2026-10-25)

The production Core now keeps a stack of immutable named database snapshots.
SAVEPOINT opens a transaction if needed. ROLLBACK TO restores the newest matching
mark and removes younger marks, while retaining the target. RELEASE removes the
target and younger marks; only release of the mark that opened the transaction
commits it. Within BEGIN, releasing all named marks leaves BEGIN active. COMMIT
and full ROLLBACK discard every named mark. Duplicate names and ASCII case
matching follow [SQLite's savepoint rules](https://www.sqlite.org/lang_savepoint.html).

The parser and independent token replay cover optional SAVEPOINT/TRANSACTION
words and the shared SQLite name grammar. Quoted keyword names remain valid;
reserved bare keywords are rejected. Core component proofs establish push/open,
release-after-push, rollback-after-push, release preserving the current database,
restoration of the exact named snapshot and ownership of the outer transaction.
Both file engines use the same RELEASE persistence decision. The legacy test
interpreter explicitly rejects the new statements; public execution stays in Core.

Baseline seed 354260 records **234 comparisons / 156 differences**. Development
seed 354261 passes **366 / 0**; the earlier expanded corpus, seed 354262, passes
**3,384 / 0**. An independent keyword-name corpus exposed **384 / 144** differences
on that source. The report is retained, and the parser/replay fix was evaluated
again on fresh examples rather than treating the earlier passing corpus as full
coverage.

Final-checkpoint fresh seed **354265** passes **1,944 / 0**, including **336**
expected errors. Twelve C-created fixtures cover three page sizes, both file
modes, nested/duplicate names, repeated rollback, schema changes, AUTOINCREMENT
history, reads during a transaction, failed statements and abandoned transactions.
Comparisons include successful output, error status, C catalog/pragma/typed-row/
integrity observations, subsequent C writes and Lean reopening. Fresh name seed
**354266** passes **504 / 0**; AUTOINCREMENT regression seed **354267** passes
**498 / 0**, on the same final source.

A live-connection executable regression additionally checks unchanged physical
bytes after inner RELEASE, state preservation after a missing-savepoint error,
rollback of sequence history, visibility to C after outer RELEASE and the
continued activity of an enclosing BEGIN.

Implementation SHA-256: `6689d98ebd32b65f640803319971eaf0afd5d7e5f7cdda6e97e21c84cd40a2b3`.
Final checks pass **338 build jobs, 248 executable tests, 1,184 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. Reports: `sqlite-savepoint-*20261025.json`; harnesses:
`scripts/run-savepoint-differential.py` and `scripts/run-savepoint-name-differential.py`.
These are scoped SQL/file/component results. Read-only transaction publication,
transaction lock modes, concurrent SQLite WAL coordination, exact diagnostics
and the remaining SQL features are separate work. Native bindings are unchanged.

## Read-only transaction publication and file access (2026-10-25)

COMMIT and transaction-owning RELEASE now publish only when the logical database
contents differ from the saved transaction snapshot. Read-only transactions and
transactions restored to their starting contents leave main/WAL bytes unchanged.
A component theorem connects logical equivalence to this decision, with separate
COMMIT and RELEASE no-publication corollaries. Changed transactions retain the
existing file/WAL publication path.

The CLI's line preflight now classifies every statement through the certified
parser. BEGIN/SAVEPOINT and other transaction controls no longer make a read-only
line demand write access. A write later on the same physical line is still
recognized and rejected on a read-only file before it can change storage.

Baseline seed 354270 records **240 comparisons / 204 differences**, including
unnecessary main/WAL changes and rejected reads on read-only files. Expanded
development seed 354271 passes **528 / 0**. Final-checkpoint fresh seed **354272**
passes **1,488 / 0** across 512/4096/65536-byte pages, both file modes, writable and
read-only files, single-line and multiline scripts and randomly nested read
transactions. All cases require unchanged main/WAL hashes and independent C
integrity/typed-row observations. The corpus also includes 48 actual write
attempts on read-only files; both engines reject them and preserve the bytes.
SAVEPOINT regression seed **354273** passes **486 / 0** on the same source.

Implementation SHA-256: `ff52894df149d16b673509813d7625a95f641e4b92072d631849ce6ce3551279`.
Final checks pass **338 build jobs, 249 executable tests, 1,187 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. Reports: `sqlite-read-transaction-*20261025.json`; harness:
`scripts/run-read-transaction-differential.py`. This decision compares complete
logical contents; no constant-time performance claim is made. It does not claim
identical physical change counters for transactions that write and later restore
the same values, concurrent SQLite WAL coordination, or complete SQL equivalence.

## Committed prefixes of failing SQL scripts (2026-10-25)

Both production file engines now admit and execute source statements incrementally.
A later syntax or lexical error preserves earlier committed writes. An open
transaction remains live on a retained Core connection after a parse error, and
its pending changes remain unpublished. The CLI's file mode processes the same
source chunks; WAL writer classification includes valid mutating statements even
when a later chunk cannot be parsed.

The pure Script scanner retains every original character, including whitespace,
comments and literal spelling. Semicolons inside quoted strings, double/backtick/
bracket identifiers and comments stay in their source group. Registered component
proofs establish per-character preservation, complete source reconstruction and
protection of grouped semicolons. Every chunk still goes through the independent
certified lexer/parser. The audit checks the actual chunk admission calls and
the source-preserving splitter on both engines. This is the admitted Core grammar;
trigger-body BEGIN/END statement boundaries remain part of future trigger support.

The original baseline report recorded **516 / 339** failures. A review found that
the inherited harness incorrectly required unchanged bytes for any failing
single-line input, including multi-statement scripts whose successful CREATE and
INSERT prefix C had persisted. The preserved raw baseline has **291 logical
observation differences** plus **48 incorrect byte-invariant-only failures**.
The first development report recorded **636 / 216**; all 216 failures came solely
from that invalid invariant, with zero logical observation differences. The
retrospective review is explicitly labeled and is not a fresh evaluation.

The corrected harness always compares complete independent C persisted
observations, and requires unchanged Lean bytes when the reference C execution
leaves its own main/WAL image unchanged. Corrected development seed 354282 passes
**696 / 0**. Final-checkpoint fresh seed **354283** passes **3,024 / 0**, including
**2880** expected errors, on twelve C-created fixtures and both file modes.
Successful output, error status, catalog/pragma/typed rows, integrity, subsequent
C writes and Lean reopens are checked. Read-transaction regression seed **354284**
passes **768 / 0**; SAVEPOINT regression seed **354285** passes **366 / 0**.

Implementation SHA-256: `7d8f1f86be35796656c2a867d462e3fefc56972b2d6fddf3efe03a0193f17188`.
Final checks pass **340 build jobs, 250 executable tests, 1,190 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. Live-connection tests cover durable prefixes, lexical errors,
retained transactions and C reads of file/WAL results. Reports:
`sqlite-script-error-*20261025.json`; harness: `scripts/run-script-error-differential.py`.
Native bindings are unchanged. Exact diagnostics, partial CLI output before an
error, trigger execution and concurrent SQLite WAL coordination are outside this
scoped result; full SQLite compatibility remains unestablished.

## SQLite identifier roles and contextual aliases (2026-10-25)

The parser and independent token replay now share SQLite's nm and ids roles.
Bare reserved keywords are rejected as declarations; INDEXED and join-kind
keywords remain valid in explicit AS aliases but not implicit aliases or type
words. Quoted table aliases work without AS. OFFSET/ASC/DESC fallback names and
single-quoted qualified column/star references are admitted. Alias spelling is
checked exactly because it is retained output metadata.

FILTER and OVER after a function call follow tokenize.c lookahead rules, so
ordinary aliases are not consumed as incomplete aggregate/window syntax. The
expression-leading CAST/RAISE/clock keywords cannot silently become column
references. REGEXP is recognized as an infix operation instead of an implicit
result alias; this change does not implement regular-expression evaluation.
The clock and window functions themselves remain separate unsupported work.
Six registered component propositions cover the admitted-name relation and
keyword/quoted/string roles; they are not a proof of the complete SQLite grammar.

The original baseline records **2,156 comparisons / 706 differences**. The first
development corpus passes **2,268 / 0** but targeted tests exposed OFFSET
qualifiers and function aliases not covered by it. The expanded all-keyword
corpus records **6,178 / 12** remaining differences (clock/RAISE qualifiers and
REGEXP mistaken for an alias). Both negative reports and targeted diagnostics
are retained. Final-checkpoint evaluation additionally includes single/backtick/
bracket quoted qualifiers and randomized names on fresh C-created fixtures.

Final-checkpoint fresh seed **354293** passes **19,410 / 0**, on three new
C-created fixtures with 512/4096/65536-byte pages and both production file modes.
Column-type regression seed **354294** passes **972 / 0** on the same source.
Final checks pass **342 build jobs, 251 executable tests, 1,196 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. Implementation SHA-256: `1fdc2e63baf4b38d6c166efbeac895e6bb1eaaa5cc591185d5abbad2b6d764c5`.
Reports: `sqlite-identifier-*20261025.json`; harness:
`scripts/run-identifier-grammar-differential.py`.

The corpus compares complete successful output, error status, C catalog/pragma/
typed-row/integrity observations, C follow-up writes and Lean reopening. It uses
all 148 keyword spellings in the pinned source (including optional WITHIN),
non-keyword/Unicode/empty names and multiple quoting forms. Exact diagnostics,
concurrent WAL coordination, clock/window/regexp evaluation and the rest of SQL
remain outside this scoped result. Native bindings are unchanged.

## CAST type grammar and expression affinity (2026-10-25)

CAST now accepts the complete admitted typetoken shape used by SQLite 3.53.4:
empty, multiword and quoted type names, with an optional one/two-number precision
suffix. The parser captures the exact span through the last significant token;
the independent token checker scans the span separately, validates its grammar
and checks the effective type retained in the AST. Invalid dimensions, misplaced
keywords and adjacent blob tokens remain errors.

Expression type interpretation follows parse.y/expr.c/sqlite3Dequote rather than
column metadata normalization. An initially quoted name ends at its first closing
quote, even when more type words follow. Internal comments remain in unquoted
type spans and can therefore affect affinity; trailing comments are outside the
span. Empty CAST types have NUMERIC affinity, unlike an undeclared table column.
Both conversion and comparison/CTAS expression affinity use this distinction.
The CAST shape and values agree with the [SQLite CAST specification](https://www.sqlite.org/lang_expr.html#castexpr)
and the pinned source; scalar conversion remains pure Lean.

Baseline seed **354300** records **840 comparisons / 450 differences**. Development
seed **354301** passes **940 / 0**. Final-checkpoint fresh seed **354302** passes
**3,420 / 0**, including **930** expected errors, across new C-created fixtures,
512/4096/65536-byte pages and both production file modes. Cases cover scalar
storage classes and bytes, comparisons, CTAS metadata, UPDATE/INSERT RETURNING,
DEFAULT evaluation, persisted typed rows, C integrity, later C writes and Lean
reopening. Column-type regression seed **354303** passes **972 / 0** on the same
source. The original negative baseline is retained.

Implementation SHA-256: `9b87c4c85276b2f258c234c7b8cb26b981c6caf9e51a1935d5641830808afa8a`.
Final checks pass **344 build jobs, 252 executable tests, 1,200 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. Four new component propositions establish successful type validation,
effective-name retention and empty/nonempty expression affinity. Executable tests
also reject forged CAST semantics during independent token replay. Reports:
`sqlite-cast-type-*20261025.json`; harness: `scripts/run-cast-type-differential.py`.
These are scoped SQL/file/component results; they do not establish complete SQL
or concurrent WAL equivalence. Native bindings are unchanged.

## Completed-statement output and runtime read-only access (2026-10-25)

The CLI now emits each completed statement's results before executing the next.
Later syntax, lexical, constraint or evaluation errors preserve that output.
The WAL engine's observed entry point retains one transaction state between
source chunks and delivers results after any required publication; its original
collecting API remains available. Printed uncommitted transaction results do not
publish pending rows. The optional cold read path still prints only after it has
handled the entire read batch, so falling back cannot duplicate output.

Write-access checks now run at actual Core statement dispatch in both file
engines, with the optional page-local INSERT path covered as well. An existing
file is opened read/write without changing bytes before a mutating statement.
Pure read statements and schema no-ops skip this check. Consequently a read-only
file accepts existing-object CREATE IF NOT EXISTS and absent-object DROP IF
EXISTS, while actual writes still fail even when their parent directory permits
atomic replacement. Two component propositions establish the shared predicate's
read-only and schema-no-op cases; they do not prove OS permission enforcement.

The original baseline records **372 comparisons / 356 differences**. Expanded
development seed **354311** passes **1,296 / 0**. Final-checkpoint fresh seed
**354312** passes **3,192 / 0** on six new C-created fixtures, 512/4096/65536-byte
input pages, both file modes, and writable/read-only variants. The harness
compares complete stdout even on errors, as well as error status, independent
C catalog/pragma/typed-row/integrity observations, later C writes and Lean reopens.
Read-transaction regression seed **354313** passes **576 / 0**, including exact
main/WAL image immutability. A public-CLI executable test checks both modes for
output from pending transaction rows followed by an error, then verifies with C
that those rows were never published.

Implementation SHA-256: `f3e332215349eedfa6fef171503ddebcc90cbd071dd3a8d2f9e29559ee3a4b24`.
Final checks pass **344 build jobs, 253 executable tests, 1,202 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. The first live-path audit rejected the new unclassified observer
entry; its failing report and log are retained. The executable-boundary registry
now explicitly classifies that IO wrapper, and the affected audit passes on
rerun. Native bindings are unchanged. Reports: `sqlite-script-output-*20261025.*`;
harness: `scripts/run-script-output-differential.py`.

This covers results of completed statements. Rows emitted by C before an error
inside the same still-running SELECT remain a separate limitation, as do exact
diagnostics, complete SQL coverage and concurrent SQLite WAL coordination.


## DEFERRED transactions and ignored transaction names (2026-10-25)

BEGIN accepts the explicit DEFERRED spelling. BEGIN, COMMIT/END and ROLLBACK
accept an optional TRANSACTION followed by an optional SQLite nm token; that
name is ignored, as in the pinned parse.y grammar. ROLLBACK TRANSACTION name TO
SAVEPOINT mark retains the actual savepoint target. The independent token replay
checks this grammar separately. IMMEDIATE and EXCLUSIVE are still rejected;
this change does not implement their locking semantics.

Baseline seed **354320** records **1,040 comparisons / 712 differences**.
Development seed **354321** records **1,136 / 330**. Those 330 negatives expose a
separate CLI behavior: after a write-access error, the C shell can execute later
statements in the same physical input line, whereas this CLI stops. Their full
reports are retained and they remain unresolved. For the transaction-name
comparison, the harness now sends each complete SQL statement on its own input
line to both engines, so C -bail stops at that statement boundary. This is an
explicit input-protocol change, not a claim to fix the old 330 counterexamples.
The line-batched development seed **354322** passes **1,184 / 0**.

Final-checkpoint fresh seed **354323** passes **3,984 / 0**, across three newly
created fixtures, 512/4096/65536-byte input pages, both production file modes,
and writable/read-only variants. Complete stdout, including error prefixes,
error status, independent C catalog/pragma/typed-row/integrity observations,
C follow-up writes and Lean reopens are compared. SAVEPOINT regression seed
**354324** passes **294 / 0** on the same checkpoint. All **344 build jobs,
254 executable tests, 1,202 headline component proofs**, both audits and
61 accepted reverse-file cells pass, with two reverse cells declared unsupported.
No new general equivalence theorem is claimed by this grammar extension.

Implementation SHA-256: `a16920c9237be2658fb4af188cb28f841cb1f7cfcecb720ba5eb023d42b33d58`.
Reports: `sqlite-transaction-name-*20261025.json`; harness:
`scripts/run-transaction-name-differential.py`. Native bindings are unchanged.
Full SQL coverage, same-line CLI continuation, partial output within a failing
SELECT and concurrent SQLite WAL coordination remain outstanding.


## Constant LIMIT/OFFSET expressions and zero-row publication (2026-10-25)

LIMIT and OFFSET now evaluate admitted deterministic scalar expressions, with
SQLite numeric affinity and signed-64-bit integer validation. Numeric text and
integral reals work; fractional, NULL, BLOB and out-of-range results fail. The
comma spelling preserves its reversed count/offset order. Both expression trees
are retained in the AST and independently replayed against source tokens before
the normalized execution window is accepted. A zero count skips offset execution,
while preparation still rejects unsupported names/functions. These rules follow
the [SQLite LIMIT specification](https://www.sqlite.org/lang_select.html#the_limit_clause)
and pinned OP_MustBeInt / computeLimitRegisters implementation.

CTAS retains failed constant expressions rather than rejecting them during broad
parsing. Its certified token replay still checks all source expressions and their
normalized fields. Runtime CTAS rejects their failed validation only after the
existing-table no-op decision; ordinary SELECT admission rejects them directly.
Thus CREATE TABLE IF NOT EXISTS on an existing table ignores an unused LIMIT
error while still rejecting malformed syntax. The legacy conformance engine also
validates the retained expressions; it is not used by the public executable.

Zero-row INSERT/UPDATE/DELETE now skip physical publication only when their
reported change count is zero and their complete logical database is unchanged.
AUTOINCREMENT can create or advance sqlite_sequence even with zero returned
rows, so the logical-content check is necessary. COMMIT and RELEASE retain their
snapshot-based publication rules. Actual write-access checks are unchanged.

Baseline seed **354330** records **644 comparisons / 330 differences**. Expanded
development seed **354331** records **1,224 / 24**, all remaining cases being
existing-table CTAS no-ops. After that correction, seed **354332** passes
**2,592 / 0**. The first fresh seed **354333** records **5,040 / 42**: logical
results agree, but a strengthened main/WAL immutability check catches unnecessary
publication for empty INSERT SELECT statements. All negative reports are retained.

After the publication fix, final-checkpoint fresh seed **354335** passes
**5,040 / 0**, on three fresh C-created fixtures, 512/4096/65536-byte pages and
both production file modes. It compares successful output, error status, full
C catalog/pragma/typed-row/integrity observations, later C writes and Lean reopens.
Whenever C leaves its main/WAL image unchanged, Lean must also leave its own
image unchanged. AUTOINCREMENT regression seed **354336** passes **426 / 0**;
read-transaction regression seed **354337** passes **576 / 0** on the same source.
Earlier, before the publication change, integer-window regression seed **354334**
passes **410 / 0** and grouped-expression resurvey seed **354340** passes
**530 / 0**; those reports retain their distinct checkpoint hashes.

Implementation SHA-256: `6c63be9eea93447a5a90039fb6311705736391112bb9361b2423e4d1a50de76d`.
Final checks pass **346 build jobs, 256 executable tests, 1,207 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. The five new component propositions cover integer acceptance,
zero-count offset skipping, unchanged empty INSERT SELECT publication, and
exclusion of COMMIT/RELEASE from that empty-DML rule. These do not prove complete
SQLite SQL or file equivalence. Subquery/nondeterministic LIMIT expressions,
exact diagnostics, same-line CLI error continuation and concurrent WAL remain
outside this result. Native bindings are unchanged. Reports:
`sqlite-limit-expression-*20261025.json`; harness:
`scripts/run-limit-expression-differential.py`.


## Two-table join spellings and optional ON (2026-10-25)

Two-table INNER, CROSS, comma and LEFT joins now accept an omitted ON clause.
An unconstrained inner join produces the Cartesian product; an unconstrained
left join preserves a left row with NULL right values when the right table is
empty. Comma and CROSS joins also admit an explicit ON predicate. These use the
existing Core join evaluator and its optimizer refinement.

A shared pure join-type classifier follows sqlite3JoinType: at most three join
keywords, repeated/reordered keywords allowed, INNER/CROSS excluded from outer
join combinations, and OUTER requiring a direction. The parser and independent
token replay both check the resulting flags. CROSS is retained explicitly in
TableRef; replay rejects changes to it and to the predicate. The first source
cannot carry fabricated join attributes. See SQLite's
[join syntax deviations](https://www.sqlite.org/lang_select.html#strange_join_names).
NATURAL and RIGHT/FULL classifications remain parseable but their execution is
still outside this admitted two-table subset, as are USING and larger joins.

Baseline seed **354350** records **1,376 comparisons / 400 differences**.
Development seed **354351** passes **1,760 / 0**. Final-checkpoint fresh seed
**354352** passes **3,776 / 0**, plus 16 immutable-image/integrity checks, across
eight newly created fixtures, empty and nonempty tables, 512/4096/65536-byte
pages and both production file modes. It covers every zero-to-three-word
combination of INNER/CROSS/LEFT/OUTER, including invalid forms, and randomized
predicates/projections/LIMITs. Complete successful output, error status, typed
C observations and unchanged main/WAL bytes are compared. Compound-collation
regression seed **354353** passes **1,256 / 0** on the same checkpoint.

Implementation SHA-256: `d70474c59b7442618298481394d5bab245401a841c381552770be4ffe7d655d6`.
Final checks pass **348 build jobs, 257 executable tests, 1,210 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. New component propositions cover the join-keyword length bound,
unconstrained row selection and an empty right side of an unconstrained LEFT
join. They are not a complete SQLite join equivalence proof. Native bindings
are unchanged. Reports: `sqlite-join-syntax-*20261025.json`; harness:
`scripts/run-join-syntax-differential.py`.


## Stored-column comparison affinity in joins (2026-10-25)

Join comparisons can now convert a stored column when SQLite comparison affinity
requires it. A typed column operand applies the existing pure physical comparison
conversion at evaluation time. The original stored/projected value is retained.
Numeric-looking text, malformed text, BLOBs and NULL therefore keep their distinct
roles. Columns whose canonical affinity already agrees still use their existing
operand and access paths. The selection follows the pinned
[SQLite comparison-affinity rules](https://www.sqlite.org/datatype3.html#type_conversions_prior_to_comparison).

The optimizer denotation and bidirectional join bridge now represent this typed
operand explicitly. Their value and round-trip proofs cover the new constructor,
and the existing left-only predicate proof still holds. A separate component
proposition shows that conversion preserves a NULL operand, including outer-join
padding. The cold path continues to decline plans it cannot execute.

Baseline seed **354360** records **2,592 comparisons / 1,296 differences**, all
valid C queries rejected by the old stored-column conversion guard. Development
seed **354361** passes **3,888 / 0**, including empty right-side tables. Final-
checkpoint fresh seed **354362** passes **5,184 / 0**, plus 72 immutable-image/
integrity checks. It covers all ordered pairs of INTEGER/NUMERIC/REAL/TEXT/BLOB/
undeclared types, both operand orders, six comparisons, INNER/LEFT and WHERE
contexts, signed integer boundaries, numeric text with embedded NUL, BLOBs and
new randomized numeric values. Input pages are 512/4096/65536 bytes, with both
production file modes. Complete successful CLI bytes are compared before large
passing captures are stored as length/SHA-256; all failing captures remain whole.
Typed independent C observations and main/WAL immutability are checked.
Join-syntax regression seed **354363** passes **1,504 / 0**, plus eight image checks.

Implementation SHA-256: `e65e4754733fba057ce88b9914ee85256ef074a4cfc08bb019d11bd7a2251519`.
Final checks pass **348 build jobs, 258 executable tests, 1,213 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. The three newly registered headline propositions are the NULL
property and the two extended optimizer bridge properties; they do not establish
whole-SQLite equivalence. Arbitrary scalar join expressions, explicit join
collations, USING/NATURAL and RIGHT/FULL execution remain separate work. Native
bindings are unchanged. Reports: `sqlite-join-affinity-*20261025.json`; harness:
`scripts/run-join-affinity-differential.py`.


## USING/NATURAL joins and merged result columns (2026-10-25)

Two-source INNER, CROSS, comma and LEFT joins now execute USING and NATURAL.
`CoreJoinUsing` resolves only declared visible columns, keeps each original name
and both physical positions, and drives equality predicates, unqualified name
binding, star expansion and CREATE TABLE AS SELECT metadata. Qualified stars
retain both tables' columns; an unqualified star suppresses the right shared
column. Implicit rowid aliases neither create natural matches nor become legal
USING columns. A merged declared key does not accidentally merge the rowid name.
Ordinary stored-column comparison affinity applies before LEFT null-extension.

The parser and independent token replay retain USING names and NATURAL flags.
NATURAL plus ON/USING is a semantic error, deferred past an existing-table CTAS
no-op just as in the pinned C engine; ON followed by USING is invalid syntax and
is still rejected before that no-op. The legacy test-only evaluator retains its
semantic validation. Public execution continues through the Core.

Baseline seed **354370** records **572 comparisons / 368 differences**, all
valid C statements rejected by the earlier join admission. Development seed
**354371** passes **1,424 / 0** after adding CTAS no-op cases. Final-checkpoint
fresh seed **354372** passes **4,368 / 0**, across six new fixtures and both
production file modes. It covers duplicate/case-varied/quoted USING names,
missing/ambiguous names, numeric comparison affinity, INTEGER and TEXT primary
keys, empty sides, natural joins with no common columns, and 512/4096/65536-byte
input pages. Complete successful output and error status are compared, followed
by independent C catalog/column/index/typed-row/integrity observations, C writes,
and Lean reopening. Main/WAL bytes must remain unchanged whenever C leaves its
image unchanged. CTAS regression seed **354373** passes **252 / 0**.

Implementation SHA-256: `9e7a0282595b6099bfd1e476aede42958f0ed4af06ef1f56eb08029a6de6ae80`.
Final checks pass **350 build jobs, 259 executable tests, 1,214 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. The new proposition proves that shared-column lookup selects a
visible schema position. Existing join optimization and SQL read refinements
continue to compile with the expanded admitted domain; this does not prove full
SQLite join equivalence. RIGHT/FULL, larger joins, general scalar join expressions,
DISTINCT/OFFSET and join ORDER BY aliases remain separate work. No native binding
changed. Reports: `sqlite-join-using-*20261025.json`; harness:
`scripts/run-join-using-differential.py`.


## Joined DISTINCT and LIMIT/OFFSET (2026-10-25)

Two-source joins now accept DISTINCT and a normalized OFFSET. Duplicate removal
uses the existing SQL numeric keys, retaining original INTEGER/REAL/TEXT/BLOB/
NULL representatives and the joined source row needed by subsequent ordering.
The common join finish path then sorts, drops OFFSET and applies LIMIT. Merge,
nested-loop and cold primary-key candidate paths all share that finish path.
See SQLite's [DISTINCT rules](https://www.sqlite.org/lang_select.html#removal_of_duplicate_rows_distinct_processing)
and [LIMIT/OFFSET rules](https://www.sqlite.org/lang_select.html#the_limit_clause).

Original representatives depend on physical scan order. A leading rowid ORDER
term can reverse an outer table scan; an inner rowid term can reverse the inner
scan. INNER joins can exchange sources when this satisfies the complete order;
CROSS and LEFT retain their outer source. A rowid equality conjunct makes later
terms constant within each pair. Partial sorting retains the applicable original
inner traversal. This recognition is explicit query metadata, derived from SQL
references, join kind, predicate and schema, and never from comparison output.
The new input-order proposition proves that it only permutes candidate pairs.
This is not a port or equivalence proof of SQLite's complete cost planner.

Baseline seed **354380** records **4,400 comparisons / 3,600 differences**.
The initial development seed **354381** passed **4,592 / 0**, but fresh seed
**354382** found **6 differences in 10,080 cases**: reverse rowid scans selected
different original DISTINCT representatives and changed later OFFSET results.
The expanded scan-order development seed **354385** then found **8 differences
in 10,848 cases**, identifying source exchanges that could not satisfy the
complete ORDER BY. Both negative reports and their checkpoint hashes remain.

Final-checkpoint fresh seed **354386** passes **14,720 / 0**, plus 16 immutable-
image/integrity checks. It includes eight new C-created fixtures, empty sides,
three page sizes, both production file modes, mixed numeric/storage classes,
six join forms, source ordering in both directions, partial sorts, filters,
and literal/expression/comma LIMIT windows. Exact successful output is compared;
errors compare status. Main/WAL bytes and independent typed C observations are
unchanged. Regression replay reconstructs the original fixtures and reruns both
engines: the earlier **6 / 0** and **8 / 0** results are regression metrics,
not fresh examples. Persisted CTAS/INSERT SELECT seed **354387** passes **456 / 0**,
including C catalog/column/index/typed-row/integrity observations, follow-up C
writes and Lean reopening. The earlier 432-case write result is retained under
its original checkpoint.

Implementation SHA-256: `70882a83a6533c115820267d71a320d7c3637b9b829c3abd11fec90f0b851d06`.
Final checks pass **350 build jobs, 260 executable tests, 1,218 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. The four new propositions cover DISTINCT key coverage, key
uniqueness, zero LIMIT and scan-order permutation. Existing join/read/optimizer
refinements compile over the extended query structure. General scalar join
expressions, explicit collations, ORDER BY aliases/ordinals, RIGHT/FULL and larger
joins remain outside this checkpoint. Native bindings are unchanged. Reports:
`sqlite-join-window-*20261025.json`; harnesses:
`scripts/run-join-window-differential.py`,
`scripts/run-join-window-write-differential.py`, and
`scripts/run-saved-join-failures.py`.


## Joined ORDER BY names and positions (2026-10-25)

Join ORDER BY now resolves explicit result aliases, names introduced by star
expansion, and signed integer result positions. Names resolve before ordinal
positions, and a repeated alias chooses its first output. A plain selected
source column does not manufacture an alias that suppresses an ambiguous source
name. Positions count the expanded projection, including USING/NATURAL merged
columns. Large integer literals outside SQLite's ordinal payload, other literal
sort constants and unbound TRUE/FALSE remain constants. Declared TRUE/FALSE
columns and output aliases retain their name-binding behavior.

The result-name table is built from the same join projection used by execution.
A new component theorem proves that discarding its names recovers that projection
exactly. The parser and independent replay now both reject aliases on a result
star, including inside an existing-table CTAS no-op; `SELECT * AS name` is invalid
SQLite syntax. Ordinary column aliases continue to work.

Baseline seed **354390** records **4,620 comparisons / 2,252 differences**, all
valid C statements rejected by the old join order translator. Its original
checkpoint hash is retained. Development seed **354391** passes **7,050 / 0**
after expanding the corpus with Boolean column names and invalid star aliases.
Final-checkpoint fresh seed **354392** passes **19,568 / 0**, plus 16 immutable-
image/integrity checks, across eight C-created fixtures, empty sides, three page
sizes and both production file modes. It covers aliases shadowing source names,
quoted/duplicate aliases, reordered stars, missing/ambiguous names, position
boundaries, constant terms, and randomized LIMIT/OFFSET. Typed C observations
and main/WAL immutability are checked. Persisted CTAS seed **354393** passes
**420 / 0**, including independent C metadata/typed-row/integrity observations,
follow-up C writes and Lean reopening. Join-window regression seed **354394**
passes **6,912 / 0**, plus eight immutable-image checks, on the same checkpoint.

Implementation SHA-256: `c62d24a7127306d3a817c1fda6f5b182f25595cfcb4e2a16a1e7ea134e8edee4`.
Final checks pass **350 build jobs, 261 executable tests, 1,219 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. The new theorem relates result-name metadata to projection; it is
not a cross-language name-resolution proof. Non-default NULL placement, explicit
join ordering collations and general scalar sort expressions remain separate
work. Native bindings are unchanged. Reports: `sqlite-join-order-*20261025.json`;
harnesses: `scripts/run-join-order-differential.py` and
`scripts/run-join-order-write-differential.py`.


## Joined NULL placement and ordering collations (2026-10-25)

Join sort terms now carry a column reference, direction, optional NULL placement
and BINARY/NOCASE/RTRIM collation. NULL placement is applied independently of
direction; non-NULL comparison reuses the existing pure byte/numeric collation
implementation. The stable sorter uses these terms, while physical scan-order
metadata remains separate for DISTINCT representative selection. Aliases and
ordinals resolve through the existing expanded projection after ordering
COLLATE wrappers are interpreted. Unknown collations are validated even for
constant sort terms and zero LIMIT. CTAS schema no-ops still defer semantic
validation until after the existing-table decision.

Baseline seed **354400** records **5,900 comparisons / 4,060 differences**.
Development seed **354401** passes **9,042 / 0**. Final-checkpoint fresh seed
**354402** passes **24,624 / 0**, plus 16 immutable-image/integrity checks.
Eight C-created fixtures cover empty and nonempty joins, three page sizes,
both file modes, mixed numeric/text/BLOB/NULL data, case and trailing-space
comparisons, embedded NUL text, both directions, all NULL-placement forms,
quoted/nested/unknown collations, aliases, ordinals, DISTINCT and windows.
Complete successful CLI bytes and error status are compared, with independent
typed C observations and immutable main/WAL images. Large passing captures are
hashed only after full comparison; failing captures are retained whole.
Persisted CTAS seed **354403** passes **840 / 0**, including C metadata/typed-row/
integrity observations, C follow-up writes and Lean reopening. ORDER BY name/
position regression seed **354404** passes **9,464 / 0**, plus eight image checks.

Implementation SHA-256: `ba090f3219ae89f538c381287f7dbd26832d82105199584e5870d6117ab83570`.
Final checks pass **350 build jobs, 262 executable tests, 1,221 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. The two new propositions specify NULL placement against a present
value in both operand orders. Existing sort-permutation and join/read/optimizer
refinements compile with the extended sort terms. These are component claims,
not a full SQLite collation or SQL equivalence proof. Projection/comparison
collations, general scalar join expressions and wider join forms remain separate
work. Native bindings are unchanged. Reports: `sqlite-join-sort-*20261025.json`;
harnesses: `scripts/run-join-sort-differential.py` and
`scripts/run-join-sort-write-differential.py`.


## Joined literal and quoted/Boolean atoms (2026-10-25)

Joined projections now share the existing operand representation for source
columns and literal values. Literal INTEGER/REAL/TEXT/BLOB/NULL and unary atoms
participate in DISTINCT, aliases, result-position ordering, compounds and
LIMIT/OFFSET. Ordering by a literal output remains a constant term. Source
columns retain their original stored values, including LEFT JOIN NULL padding.

Schema-dependent name binding precedes join operand/projection translation.
Quoted identifiers resolve as columns, and a declared TRUE/FALSE column shadows
its Boolean keyword. Ambiguous names still fail, including on empty results.
The grammar's positive bound-name constructor records this normalization; the
existing no-explicit-projection-collation proof is preserved through it.

Baseline seed **354410** records **4,980 comparisons / 3,664 differences**:
3,654 rejected valid statements, eight accepted invalid statements and two
successful queries with wrong rows from Boolean column shadowing. Development
seed **354411** passes **6,084 / 0**. Final-checkpoint fresh seed **354412** passes
**17,184 / 0**, plus 16 immutable-image/integrity checks. Eight new C-created
fixtures cover empty sides, three input page sizes, both production file modes,
mixed storage classes, Boolean column presence/ambiguity, merged names, outer
padding, DISTINCT, aliases, ordering positions, compound outputs and windows.
Complete successful output and error status are compared; independent C typed
observations and unchanged main/WAL bytes are checked. Persisted CTAS/INSERT
SELECT seed **354413** passes **1,008 / 0**, including independent C metadata,
typed rows, integrity, follow-up writes and Lean reopening. Join sort regression
seed **354414** passes **11,992 / 0**, plus eight immutable-image checks.

Implementation SHA-256: `c4f887a4e4c53c8380d365db9db3ac8c3d120d39fc16a5f33208666571e93c58`.
Final checks pass **350 build jobs, 263 executable tests, 1,222 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. The new component theorem proves that embedding existing column
projections in operand projections preserves every value. Existing join/read/
optimizer refinements compile with the extended projection; this does not prove
complete SQLite expression equivalence. General scalar expressions over joined
columns, projection/comparison collations and wider join forms remain separate
work. Native bindings are unchanged. Reports: `sqlite-join-atoms-*20261025.json`;
harnesses: `scripts/run-join-atoms-differential.py` and
`scripts/run-join-atoms-write-differential.py`.


## Visible SQL columns and implicit rowid names (2026-10-25)

SQL name lookup now searches visible schema positions before falling back to
`rowid`, `oid` or `_rowid_`. The internal bookkeeping column is absent from that
lookup. CoreSQL, row-expression binding and USING/NATURAL metadata share this
visible-column implementation. Index declarations retain their declared-only
lookup. Output aliases remain independent, and an explicitly declared column
with the internal spelling remains accessible in schemas with an INTEGER
PRIMARY KEY. See SQLite's [rowid naming rules](https://www.sqlite.org/lang_createtable.html#rowid).

Baseline seed **354420** records **100 comparisons / 48 differences**, including
reads and writes through the internal bookkeeping name. Development seed
**354421** passes **372 / 0**. Final-checkpoint fresh seed **354422** passes
**1,312 / 0**, across eight C-created fixtures, three input page sizes and both
production file modes. It covers empty/nonempty tables, quoted/case-varied names,
projections, sorting, grouping, predicates, joins, dead expression branches,
RETURNING, assignment/insert targets, index declarations, CTAS and schema edits.
Positive controls exercise declared names, output aliases and all three rowid
spellings, including their shadowing by declared columns. Complete successful
output and error status are compared, together with independent C catalog,
column/index metadata, typed rows, integrity, follow-up writes and Lean reopening.
Main/WAL images must remain unchanged whenever C leaves them unchanged.
Joined-atom regression seed **354423** passes **8,272 / 0**, plus eight immutable-
image checks.

Implementation SHA-256: `c0aa7522986a9d83943812e7c8d263cafed16458595818ca955eab74982b09bd`.
Final checks pass **350 build jobs, 264 executable tests, 1,224 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. Two new component propositions restrict declared-name results to
visible positions and general lookup results to visible positions or explicit
rowid aliases. These are internal lookup claims, not complete SQLite name-
resolution equivalence. A declared `__sqleanite_rowid` still cannot coexist with
an additional hidden bookkeeping column; cross-source declared-rowid priority
remains separate work. Native bindings are unchanged. Reports:
`sqlite-column-visibility-*20261025.json`; harness:
`scripts/run-column-visibility-differential.py`.


## Declared rowid names across joined sources (2026-10-25)

Join name resolution now searches all eligible sources for declared columns
before falling back to implicit rowid spellings. A declared `rowid`, `oid` or
`_rowid_` on one side therefore takes precedence over the other side's implicit
alias. Qualified references remain source-local; multiple declared matches
still require USING/NATURAL merging or produce ambiguity. The shared candidate
resolver also drives CTAS column names and affinities. Its component theorem
states that a nonempty declared candidate list is returned unchanged.

Baseline seed **354430** records **568 comparisons / 172 differences**, all
valid C statements rejected as ambiguous. Initial development seed **354431**
records **948 / 2** after name binding was corrected. Those two exact-output
differences exposed the right scan used when the left rowid is probed from a
right-side value. The recognized scan order is now explicit query metadata,
applied before DISTINCT, stable output sorting and windows. CROSS/LEFT joins
retain their fixed outer source; two-rowid equalities retain the existing scan
recognition. A permutation theorem states that this ordering retains all input
pairs. This recognition is not SQLite's full cost planner, and it does not add
a new indexed access implementation. Expanded scan development seed **354434**
passes **1,488 / 0**; exact replay of the two earlier failures passes **2 / 0**.

Final-checkpoint fresh seed **354432** records **3,360 / 2**. The two remaining
exact-output differences occur in one fixture in both file modes: an automatic
covering index changes the order of rows tied on `ORDER BY rowid`. Full rows
agree as a multiset, but the primary exact-output metric remains a failure.
A separately labelled diagnostic replay adds unique `a.id,b.id` tie breakers
and passes **2 / 0**; that control is neither a fresh evaluation nor a replacement
for the two negative results. Automatic-index traversal remains open work.

The fresh corpus uses twelve new C-created fixtures covering all three rowid
spellings, neither/one/both sources declaring them, mixed affinities, empty sides,
three page sizes, both file modes, qualified/quoted names, USING/NATURAL, CTAS,
filters and LIMIT/OFFSET. Successful output/error status is compared together
with independent C catalog/column/index metadata, typed rows, integrity,
follow-up writes and Lean reopening. Immutable main/WAL images are checked
whenever C leaves its image unchanged. DISTINCT/window regression seed **354435**
passes **6,912 / 0**, plus eight immutable-image checks. Joined-atom write
regression seed **354436** passes **504 / 0**.

Implementation SHA-256: `53124e866ceff943ff59d418452c774adc5788c6317603d75863226c45dc8cfb`.
Final checks pass **350 build jobs, 266 executable tests, 1,226 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. The earlier development checkpoint and both fresh negatives remain
in the reports. Native bindings are unchanged. Reports:
`sqlite-join-rowid-names-*20261025.json`; harness:
`scripts/run-join-rowid-names-differential.py`. The saved read-only failure replay
also accepts fixtures embedded in per-case file-write reports.


## Truth conversion in joined ON/WHERE (2026-10-25)

Joined predicates now admit standalone literal/column truth operands and their
AND/OR/NOT combinations. Physical truth conversion preserves NULL as UNKNOWN,
recognizes both signed REAL zeros, and reads numeric prefixes from TEXT/BLOB
bytes without changing the stored value. It shares the existing scalar numeric
scanner. The live join predicate and its optimizer embedding use this conversion;
the older abstract column-truth denotation now uses it too, instead of treating
all TEXT/BLOB values as false. Logical optimizer and cost refinements still
compile. See SQLite's [Boolean expression rules](https://www.sqlite.org/lang_expr.html#booleanexpr).

Schema-dependent binding runs before the existing parser-level preparation.
Declared TRUE/FALSE names therefore retain their column meaning. The limited
zero-AND simplification preserves SQLite's distinctions between integer zero,
Boolean keywords and expressions carrying function calls. The positive grammar
records preparation explicitly; it does not bypass the independent parser replay.

Baseline seed **354440** records **5,688 comparisons / 5,144 differences**, all
valid C statements rejected by the previous join predicate translator.
Development seed **354441** passes **4,410 / 0**. Final-checkpoint fresh seed
**354442** passes **12,400 / 0**, plus 16 immutable-image/integrity checks. Eight
new C-created fixtures cover empty sides, three page sizes, both file modes,
NULL/numeric/text/BLOB values, numeric prefixes and malformed UTF-8, embedded NUL,
subnormal/infinite REALs, Boolean-name shadowing, outer padding, logical
combinations and row windows. Complete successful output and error status are
compared, with independent C typed observations and immutable main/WAL images.
Persisted CTAS/INSERT SELECT seed **354443** passes **1,248 / 0**, including C
catalog/column/index metadata, typed rows, integrity, follow-up writes and Lean
reopening. Joined-atom regression seed **354444** passes **8,272 / 0**, plus eight
immutable-image checks.

Implementation SHA-256: `88b89c69ef1d30275f913f4cd0467e3ac4be4315111d447ad6dd33e10ac83c9c`.
Final checks pass **350 build jobs, 267 executable tests, 1,227 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. The new component proposition preserves UNKNOWN for a NULL truth
operand; the bidirectional optimizer embedding and evaluation refinements cover
the new predicate constructor. This is not complete SQLite expression or planner
equivalence. General joined row arithmetic/functions, IS comparisons and the
previously recorded automatic-index tie-order differences remain separate work.
Native bindings are unchanged. Reports: `sqlite-join-truth-*20261025.json`;
harnesses: `scripts/run-join-truth-differential.py` and
`scripts/run-join-truth-write-differential.py`.


## Joined IS comparisons, operand wrappers and comparison collations (2026-10-25)

Joined IS/IS NOT and their DISTINCT FROM spellings now use NULL-safe equality.
An unshadowed TRUE/FALSE keyword on the right instead selects a two-valued truth
conversion. COLLATE wrappers preserve that keyword role, including an otherwise
unknown collation; unary plus and probability hints retain ordinary equality.
Schema binding still precedes this decision, so declared TRUE/FALSE columns win.
The shared scalar evaluator also recognizes the collated Boolean keyword.

Join column operands now admit unary plus, COLLATE and valid likely/unlikely/
likelihood wrappers. These preserve stored values while unary plus and the hints
remove expression affinity. Comparison predicates carry BINARY/NOCASE/RTRIM
through the existing byte/numeric collation implementation; unknown required
collations fail. BINARY retains the existing predicate constructors used by the
limited scan-order recognizer. Collated predicates have optimizer denotations,
costs and bidirectional join embeddings. The positive grammar records the new
wrappers and IS forms, and existing join/read/optimizer refinements compile.

Baseline seed **354450** records **6,048 comparisons / 2,992 differences**.
Initial development seed **354451** records **10,944 / 2,242**, including 236
successful queries with wrong rows and 2,006 rejected valid statements. These
negatives exposed Boolean COLLATE handling, removed affinity and comparison
collations, and remain in the reports. Expanded development seed **354454**
passes **11,520 / 0**. Exact replay of all 2,242 saved failures passes **2,242 / 0**
on the final implementation; that is regression replay, not fresh evaluation.

Final-checkpoint fresh seed **354452** passes **31,360 / 0**, plus 16 immutable-
image/integrity checks. Persisted CTAS/INSERT SELECT seed **354453** passes
**1,824 / 0**, including independent C catalog/column/index metadata, typed rows,
integrity, follow-up writes and Lean reopening. Truth regression seed **354455**
passes **5,880 / 0**, plus eight immutable-image checks. These corpora combine
fixed controls with newly seeded data and logical combinations; the entire case
count is not a count of previously unseen inputs. They cover three page sizes,
both file modes, empty/nonempty sides, mixed storage classes, Boolean-column
shadowing, outer padding, wrappers, collation precedence and windows. Successful
CLI bytes and error status are compared without dropping any mismatches.

Implementation SHA-256: `10116d2cf02d3e178445862873755d20441baeac9cd0529517eb02182ea19da6`.
Final checks pass **350 build jobs, 269 executable tests, 1,233 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. Six new component propositions cover NULL-safe equality, NULL
truth tests, collated Boolean keywords, unary-plus affinity and the BINARY
wrapper identity. They do not prove complete SQLite expression or planner
equivalence. IN lists, general joined row arithmetic/functions, projection and
declared-column collations, and the recorded automatic-index tie-order failures
remain separate work. Native bindings are unchanged. Reports:
`sqlite-join-is-*20261025.json`; harnesses:
`scripts/run-join-is-differential.py` and
`scripts/run-join-is-write-differential.py`.


## Joined IN and NOT IN list predicates (2026-10-25)

Joined IN lists now compile to a disjunction of nullable equalities, with NOT
applied after membership. The comparison uses the left expression's affinity
and collation; right-side affinity and COLLATE metadata do not select them.
Existing parser preparation retains SQLite's distinct handling of empty lists
and a single constant choice. NULL padding from LEFT JOIN participates through
the same three-valued logic. See SQLite's [IN rules](https://www.sqlite.org/lang_expr.html#in_op)
and [comparison affinity rules](https://www.sqlite.org/datatype3.html#type_conversions_prior_to_comparison).

Baseline seed **354460** records **7,824 comparisons / 3,970 differences**, all
valid statements rejected by the prior translator. Development seed **354461**
passes **15,936 / 0**. Final-checkpoint fresh seed **354462** passes **32,832 / 0**,
plus 24 immutable-image/integrity checks. Twelve C-created fixtures cover six
column-affinity arrangements, three page sizes, both file modes, empty/nonempty
sides, mixed storage classes, zero/one/many choices, NULL, unary plus, probability
wrappers, left and ignored right collations, Boolean shadowing and windows.
The corpus combines fixed controls with newly seeded data/logical combinations;
its full case count is not a count of previously unseen inputs. Successful CLI
bytes and error status are compared without filtering mismatches. Persisted
CTAS/INSERT SELECT seed **354463** passes **1,824 / 0**, including independent C
metadata, typed rows, integrity, follow-up writes and Lean reopening.

IS regression seed **354464** records **15,360 / 2**, retained as negative results.
Both failures are the same case in the two file modes: SQLite simplifies a
literal IS NULL test before resolving an ambiguous TRUE column in an AND branch;
Lean still attempts that lookup. This is a newly exposed parser-preparation gap,
and the IS regression is not reported as passing.

A separate error-timing diagnostic, seed **354470**, records **4,032 / 2,078**.
Of those differences, 2,062 reject successful C statements and 16 disagree on
rows returned before a statement error. This diagnostic compares stdout even
when both statements fail, in addition to error status and immutable images.
It exposes eager evaluation of functions in eliminated conditions/empty lists,
runtime errors on empty input or zero LIMIT, and partial-row delivery. The
passing IN corpus above does not establish compatibility for those expression
error paths. The diagnostic and its original captures are retained for the next
work, rather than excluded from the compatibility record.

Implementation SHA-256: `952793d1149949dd21ced4ff7b41b35bae138bb7ec3e26e14136c9b8916264ff`.
Final structural checks pass **350 build jobs, 270 executable tests, 1,235 headline
component proofs**, both audits and 61 accepted reverse-file cells, with two
declared unsupported. Two new component theorems equate membership with the
ordered three-valued equality fold and specify NULL membership for empty and
nonempty choices. The positive grammar covers every admitted list operand.
These are component claims, not complete SQLite SQL or planner equivalence.
IN subqueries, general joined scalar expressions, the error-timing negatives,
and previously recorded automatic-index tie order remain open. Native bindings
are unchanged. Reports: `sqlite-join-in-*20261025.json` and
`sqlite-join-shortcircuit-baseline-20261025.json`; harnesses:
`scripts/run-join-in-differential.py`, `scripts/run-join-in-write-differential.py`
and `scripts/run-join-shortcircuit-differential.py`.


## Parser-time literal NULL tests (2026-10-25)

Scalar preparation now follows parse.y's literal-token ISNULL/NOTNULL rewrite.
INTEGER/REAL/TEXT/BLOB tokens, optionally wrapped in unary plus or minus, become
integer false/true without evaluating the token. NULL, Boolean names, COLLATE,
bitwise NOT and computed expressions retain their ordinary NULL test. Both
compact IS forms and DISTINCT FROM spellings with a bare NULL right operand use
the same preparation. A resulting zero can participate in the existing parser
AND simplification before source-name checking. This also preserves deferred
numeric-token errors when SQLite discards the literal before generating code.
The implementation rule is taken from `sqlite3PExprIsNull` and `sqlite3PExprIs`
in the pinned upstream `src/parse.y`.

Baseline seed **354480** records **7,938 comparisons / 1,506 differences**, all
valid C statements rejected by the previous preparation. Development seed
**354481** passes **10,776 / 0**. Final-checkpoint fresh seed **354482** passes
**22,192 / 0**, plus 16 immutable-image/integrity checks. The eight C-created
fixtures combine fixed literal controls and newly seeded inputs/logical
combinations; the count does not imply every input was previously unseen.
The corpus covers seven NULL-test spellings, unary token wrappers, NULL/Boolean/
column distinctions, invalid numeric tokens, discarded/unresolved/ambiguous
names, single-table and joined predicates, no-source expressions, outer padding,
three page sizes and both file modes. Successful output and error status are
compared, with independent C typed observations and immutable main/WAL images.
Persisted CTAS/INSERT SELECT seed **354483** passes **1,248 / 0**, including C
metadata, typed rows, integrity, follow-up writes and Lean reopening. IS
regression seed **354484** passes **15,552 / 0**, plus eight image checks. Exact
regression replay of the two earlier IS failures passes **2 / 0**; the original
negative report remains unchanged, and replay is not counted as fresh testing.

Implementation SHA-256: `4ce2ea9fbe87cbdf9e3448132db31daa4406533fc1cfa475926b287bd23a1f31`.
Final checks pass **350 build jobs, 271 executable tests, 1,237 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. The new component propositions specify the recognized-token
rewrite and exclude COLLATE from token recognition. They are not a complete
SQLite preparation/equivalence proof. The separate joined-function error-timing
diagnostic and automatic-index traversal gaps remain open. Native bindings are
unchanged. Reports: `sqlite-null-prepare-*20261025.json`; harnesses:
`scripts/run-null-prepare-differential.py` and
`scripts/run-null-prepare-write-differential.py`.


## Statically decided join conditions and outer-ON ordering (2026-10-25)

Joined conditions can now return a proved constant without evaluating skipped
functions. Name/arity resolution still traverses the original prepared syntax,
using the pinned builtin registry already used for ignored aggregate ordering.
Required numeric-token and collation errors are validated separately against
the operations SQLite generates. Top-level AND terms retain separate generation
checks even when an earlier false term stops runtime evaluation.

Ordinary conditions use SQLite's static truth flags. LEFT JOIN ON carries a
separate mode: upstream `ExprAlwaysTrue`/`ExprAlwaysFalse` disable those flags
under `EP_OuterON`. Its constant decision therefore proceeds left to right and
its code-generation validation retains both branches. For example,
`1 OR abs(-9223372036854775808)` skips the function at runtime, whereas the
reversed outer-ON form must evaluate that function first. Unknown function/column names and invalid
arities still fail. This also allows registered but otherwise unimplemented
functions in branches that provably never execute; no external evaluator is
called. General dynamic function execution is not added by this change.

Baseline seed **354490** records **7,680 comparisons / 3,506 differences**.
Initial development seed **354491** records **10,432 / 242**, all invalid C
statements incorrectly accepted by the first draft. That negative result exposed
the outer-ON distinction and is retained. Corrected development seed **354495**
records **10,432 / 98**: 96 rejected successful C statements and two partial-output
differences. Strict replay of the 242 original failures records **242 / 2**, with
the two remaining cases disagreeing on rows delivered before malformed-JSON
errors. The replay tool now has an explicit `--compare-error-output` option;
its historical default comparison remains available.

Final-checkpoint fresh seed **354492** records **21,504 / 204**: 200 rejected valid
statements and four partial-output differences. There are no accepted-invalid
cases in this evaluation. The remaining cases require actual function evaluation,
correct deferral on empty inputs/zero LIMIT, or partial-row delivery. Eight
C-created fixtures combine fixed controls and newly seeded inputs/combinations,
with both file modes, three page sizes, outer padding, Boolean shadowing, function
signatures, required collations and deferred numeric errors. Full stdout is
compared on success and failure, together with error status, immutable main/WAL
images and independent C typed/integrity observations. The full case count does
not mean every input was previously unseen.

Persisted CTAS/INSERT SELECT seed **354493** records **1,632 / 18**. Twelve cases
reject successful C statements; six fail in both engines but leave different
catalogs because C first completes a zero-LIMIT CTAS before the later INSERT
fails. These are retained execution-timing negatives. Independent C metadata,
typed rows, integrity, follow-up writes and Lean reopening remain part of the
comparison. IS regression seed **354494** passes **15,360 / 0**, plus eight image
checks. Broader short-circuit regression seed **354496** records **5,568 / 1,156**:
1,132 rejected successful statements, 16 partial-output differences, and eight
exact-order differences on successful queries. In those eight cases SQLite scans
the right source first despite the condition's constant result. These planner
negatives are not normalized away. All negative reports remain committed.

Implementation SHA-256: `cd5c5108be3f954236ed9dd34d41ca0c9e0c7fb2ddfd7eb94ae7b658bb0684ab`.
Final structural checks pass **352 build jobs, 272 executable tests, 1,241 headline
component proofs**, both audits and 61 accepted reverse-file cells, with two
declared unsupported. The initial live-path audit failed because its textual
check expected the old ON callback; its report is retained and the updated check
requires the actual outer-ON argument. Four new component propositions cover
ordinary static term/list evaluation, constant predicate evaluation and an
ordered decision model with arbitrary pending-atom errors. The last model is not
a complete SQLite outer-ON or query-planner equivalence proof. Dynamic joined
expressions and the recorded execution/planner negatives remain open work.
Native bindings are unchanged. Reports: `sqlite-join-static-*20261025.json`;
harnesses: `scripts/run-join-static-differential.py` and
`scripts/run-join-static-write-differential.py`.


## Zero-LIMIT joined predicate evaluation (2026-10-25)

The ordinary and cold join paths now share a zero-LIMIT fallback. Original ON
and WHERE expressions retain source-name, function-signature and generated
numeric/collation validation, including the outer-ON distinction. Only after
those checks can predicate value evaluation be omitted. Source/USING metadata,
projection and ordering still use the ordinary translator. Successful existing
translations are unchanged. This adds no dynamic function implementation.

Baseline seed **354500** records **2,736 comparisons / 858 differences**, all
successful C statements rejected by eager value evaluation or admission.
Development seed **354501** passes **3,840 / 0**. Final-checkpoint fresh seed
**354502** passes **8,320 / 0**, plus 16 immutable-image/integrity checks.
The eight C-created fixtures combine fixed controls with newly seeded inputs
and predicate combinations; not every case is previously unseen. Full stdout
and error status are compared in both file modes, across three page sizes,
including empty sources, Boolean-name shadowing, required preparation errors,
ORDER BY and OFFSET. Independent C typed observations check the source images.
Persisted CTAS/INSERT SELECT seed **354503** passes **1,632 / 0**, with C metadata,
typed rows, integrity, subsequent C writes and Lean reopening.

Static-condition writer regression seed **354504** records **1,632 / 12**.
All remaining differences reject successful C statements with an empty input
and nonzero/unlimited LEFT JOIN ON evaluation. The previous six catalog-state
differences, caused by failing an initial zero-LIMIT CTAS before a later failing
INSERT, no longer occur. The remaining negative results are preserved; this
checkpoint does not claim general empty-input or dynamic-expression equivalence.

Implementation SHA-256: `bf4cd22673473502c173c0a9765c96cd4d8b721f92aba43e51add1abb4ddf469`.
Final checks pass **352 build jobs, 273 executable tests, 1,244 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. New component propositions prove that a zero-limit query has no
output, the fallback always returns such a limit, and existing successful
translations are preserved. They are not complete SQL or planner equivalence
proofs. Native bindings are unchanged. Reports: `sqlite-join-zero-limit-*20261025.json`;
harnesses: `scripts/run-join-zero-limit-differential.py` and
`scripts/run-join-zero-limit-write-differential.py`.


## Empty-input outer-ON evaluation (2026-10-25)

A LEFT JOIN with either input empty now validates its original ON expression
without evaluating its value. The fallback is guarded by actual input emptiness
and the outer-join kind. Name/arity and outer-ON code-generation checks remain
mandatory; WHERE, projection, ordering and source metadata retain ordinary
translation. The same interpretation supplies compound-result metadata. Existing
successful translations and unsuccessful fallback diagnostics are preserved.

Baseline seed **354510** records **3,648 comparisons / 992 differences**,
including 800 empty-input failures and 192 nonempty-input controls. Development
seed **354511**, expanded with compound operations, records **4,096 / 172**.
All 172 remaining failures are nonempty-input controls: 150 rejected successful
statements and 22 partial-error-output differences. These negatives are retained.

Final-checkpoint fresh seed **354512** records **8,832 / 462**, plus 16 passing
immutable-image/integrity checks. All **6,624 empty-input comparisons pass**;
the 462 failures are rejected successful statements in nonempty-input controls.
The corpus includes fixed controls and newly seeded values/combinations, not
8,832 wholly unseen inputs. It compares full stdout/error status, NULL extension,
WHERE filters, LIMIT/OFFSET, compound operations, function/signature/collation
errors, Boolean-name shadowing and three page sizes in both file modes.
Persisted fresh seed **354513** records **1,632 / 108**. All **1,360 empty-input
write cases pass**; every remaining failure rejects a successful nonempty-input
statement. Independent C catalog/typed-row/integrity checks, subsequent C writes
and Lean reopening are included. Static-condition writer regression seed
**354514** passes **1,632 / 0**, including the fixed empty-input cases that still
failed at the previous checkpoint. This regression is reported separately from
the broader fresh corpus; the older negative reports remain unchanged.

Implementation SHA-256: `77d18c4107a089388846d585e7b36d439fddc74d98649668b10f817ee5042fd6`.
Final checks pass **352 build jobs, 274 executable tests, 1,247 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. Component theorems prove empty-left output, outer-ON independence
with an empty right input, and preservation of existing translations. They do
not establish complete upstream planner or dynamic-expression equivalence.
Native bindings are unchanged. Reports: `sqlite-join-empty-on-*20261025.json`;
harnesses: `scripts/run-join-empty-on-differential.py` and
`scripts/run-join-empty-on-write-differential.py`.


## Joined projection wrappers and result collations (2026-10-25)

Joined column/literal projections now accept leading unary plus, COLLATE and
valid likely/unlikely/likelihood wrappers. Value translation uses the existing
atom interpreter, while original expression metadata supplies DISTINCT and
ORDER BY comparison. Explicit ORDER BY collations override inherited output
collations; top-level output aliases and positions inherit them. Direct source
expressions keep their own metadata. Star expansion preserves slot order and
BINARY source metadata. Compound queries now distinguish absent result collation
from inherited BINARY: unlike a plain column or unary plus, likely(column) does
not supply the column's default collation. CTAS still derives names and affinity
from the original expressions. Invalid arities/probabilities, ordinal positions
and required collations remain errors; an unused COLLATE name need not be resolved.

The join query carries separate DISTINCT comparison kinds. Collated duplicate
elimination retains original joined rows, preserving unselected ORDER BY values
and stored bytes. The BINARY-only path retains the existing numeric-key operation.
The optimizer preserves this metadata. Existing successful SQL translations and
their fast-subset proof relation remain unchanged; the new wrapper translation
has its own fallback rather than asserting that all result collations are absent.

Baseline seed **354520** records **7,200 comparisons / 5,450 differences**, all
successful C statements previously rejected. Development seed **354521** passes
**9,792 / 0** after expanding the fixed byte-value fixture; persisted development
seed **354525** passes **1,200 / 0**. Final-checkpoint fresh seed **354522** passes
**23,104 / 0**, plus 16 immutable-image/integrity checks. This expanded corpus also
checks right-arm compound collation priority. It mixes fixed controls and newly
seeded inputs/combinations; the total is not a count of wholly unseen examples.
Coverage includes nested wrappers, aliases, ordinal/source ordering, NULL
extension, Boolean-name binding, mixed numeric storage classes, invalid UTF-8,
embedded NUL, NOCASE byte-length distinctions, RTRIM, compound sets, LIMIT/OFFSET,
three page sizes and both file modes. Full stdout and error status are compared,
with independent C typed observations of immutable source images.

Persisted fresh seed **354523** passes **3,216 / 0**, including CTAS/INSERT SELECT,
compound affinity/name metadata, typed rows, integrity, subsequent C writes and
Lean reopening. Atom regression seed **354524** passes **8,272 / 0**, plus eight
image checks. Implementation SHA-256:
`bbb0eda14bbb325dd8ebb346f66da5f8b8439d6808e5984095995553f22135f5`.
Final checks pass **352 build jobs, 275 executable tests, 1,250 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. New component theorems establish original-row retention and pairwise
absence of collated duplicates, plus preservation of existing translations.
They do not prove complete SQLite expression/planner equivalence. General joined
scalar evaluation, RIGHT/FULL joins and the recorded planner-order negatives
remain open. Native bindings are unchanged. Reports:
`sqlite-join-wrappers-*20261025.json`; harnesses:
`scripts/run-join-wrappers-differential.py` and
`scripts/run-join-wrappers-write-differential.py`.


## RIGHT/FULL joins with explicit or omitted ON (2026-10-25)

The production path now executes two-source RIGHT and FULL joins with the
existing supported predicates/projections. Matching rows retain left-scan order;
FULL also retains unmatched left rows, and both forms append unmatched right
rows. Match accounting uses ON before WHERE, so a later rejected match cannot
create a spurious unmatched right row. Missing values cover every physical
column, including rowid aliases. The shared query finisher applies result
collations, DISTINCT, ordering and windows. Left-scan ordering shortcuts are
disabled across the appended unmatched-right suffix. Compound-result metadata
uses the same outer-join translation.

Token replay still checks the classified join flags against the parsed source.
Its old unconditional RIGHT/FULL rejection has been removed. The initial
component implementation compiled but did not reach public execution because
that guard remained: seed **354531** recorded **5,056 / 4,918** differences,
writer seed **354535** recorded **1,320 / 1,296**, and the executable test failed.
Those reports and the failing check record are preserved. The earlier baseline
seed **354530** records **4,864 / 4,736**. Corrected development seed **354536**,
expanded with compounds, records **5,568 / 96**; writer seed **354537** records
**1,704 / 72**. All remaining differences are USING/NATURAL shared-name cases.

Final-checkpoint fresh seed **354532** records **12,544 / 192**, plus 16 passing
immutable-image/integrity checks. All **12,288 non-USING/NATURAL comparisons pass**.
The 192 retained failures reject successful shared-name statements. Fresh writer
seed **354533** records **3,696 / 144**, with all **3,504 non-USING/NATURAL cases
passing**; its remaining failures have the same unsupported shared-name cause.
These corpora include ordinary and unusual valid join spellings, invalid type
combinations, omitted/constant/comparison ON, NULL extension, WHERE filtering,
source emptiness, quoted/Boolean names, comparison affinity/collation, wrappers,
DISTINCT, compounds, LIMIT/OFFSET, three page sizes and both file modes. Fixed
controls and newly seeded fixtures/combinations are mixed, not all unseen cases.
Full stdout/error status, immutable source images, C metadata/typed rows,
integrity, follow-up C writes and Lean reopening are checked as applicable.
Wrapper regression seed **354534** passes **11,232 / 0**, plus eight image checks.

Implementation SHA-256: `1b55c245438d1fb11205567c0f99eaf0321cfdb5c00b874013fc2e1982ce5fe9`.
Final checks pass **354 build jobs, 276 executable tests, 1,255 headline component
proofs**, both audits and 61 accepted reverse-file cells, with two declared
unsupported. New component results characterize unmatched-right membership,
empty-side padding, output width and read-state preservation. They do not prove
full upstream SQL/planner equivalence. RIGHT/FULL USING and NATURAL remain
explicitly unsupported pending shared-column value/name/affinity binding;
general dynamic joined expressions and earlier planner-order negatives also
remain open. Native bindings are unchanged. Reports:
`sqlite-join-outer-*20261025.json`; harnesses:
`scripts/run-join-outer-differential.py` and
`scripts/run-join-outer-write-differential.py`.


## RIGHT USING/NATURAL merged columns and star metadata (2026-10-25)

Two-source RIGHT joins now resolve unqualified shared names to the right
column's value, affinity and spelling. Expanded left stars, including `left.*`,
keep their original position/name while reading the shared value from the
right. Explicit qualified references such as `left.key` retain the left value.
CTAS inherits right affinity for replaced star slots without renaming them;
qualified right stars retain their own columns. The shared bound-query
interpreter preserves outer-ON preparation, empty-side and zero-LIMIT handling,
projection wrappers, result collations, DISTINCT, ordering and windows. FULL
NATURAL with no common columns is admitted; shared FULL columns remain rejected.

Baseline seed **354540** records **2,400 cases / 1,512 differences**. Initial
development seed **354541** records **3,392 / 500**: 408 rejected successful FULL
cases and 92 incorrect qualified-left-star outputs. That negative result changed
the implementation: left-star expansion must merge even when table-qualified,
unlike an explicit qualified column. Both the initial report and the complete
baseline remain available. Corrected development seed **354546** records
**3,424 / 432**, all remaining differences being unsupported FULL shared names.
The 92 original star failures have a separate strict regression replay with
**92 / 0**; the labelled selection retains its source hash and the complete
unfiltered development report. Both C and Lean are rerun on the saved fixtures.

Final-checkpoint fresh seed **354542** records **5,616 / 660**.
All **4,416 non-FULL comparisons pass**; every retained difference rejects
a successful FULL shared-name statement. The combined corpus tests successful
stdout, error status, independent C catalog/typed-row/integrity observations,
subsequent C writes, Lean reopening and main/WAL immutability whenever C leaves
those bytes unchanged. It covers RIGHT spellings, USING duplicates and quoted
names, NATURAL, missing/implicit-rowid names, empty inputs, left/right declared
affinities, wrappers, ordering/windows, CTAS/INSERT SELECT and CTAS no-op error
deferral across three page sizes and both file modes. Fixed controls and seeded
fixtures/query combinations are mixed; this is not an entirely unseen corpus.

INNER/LEFT USING regression seed **354543** passes **3,008 / 0**. Outer-ON
regression seed **354544** records **5,952 / 48**, with only the still unsupported
FULL shared-name controls failing. Final checks pass **354 build jobs, 277
executable tests, 1,257 headline component proofs**, both audits and 61 accepted
reverse-file cells, with two declared unsupported. The new component theorems
establish right-slot selection and star-name preservation, not full SQLite
equivalence. Native bindings remain unchanged. Implementation SHA-256:
`30ba9c0ab63a87da883f0622f091b81899d2d9d0b27a1b1eecc28bf9df584771`. Reports:
`sqlite-join-right-using-*20261025.json`; combined harness:
`scripts/run-join-right-using-differential.py`.


## FULL USING/NATURAL coalesced values (2026-10-25)

The public FULL join path now supports shared USING/NATURAL columns. Bare shared
names and expanded left-star slots choose the left value when non-NULL and the
right value otherwise; explicit qualified columns and qualified right stars
retain their original source values. The merged operand inherits the left
column's comparison affinity. Comparison conversion is applied to the selected
value even when it came from a differently typed right column. Unary plus and
probability wrappers still remove affinity. ORDER BY uses the actual merged
operand, including output aliases/ordinals and explicit collations; DISTINCT
uses the same projected value and result collation.

The operand is represented in both the live Core and denotational join language,
with an extended value-preserving optimizer bridge and round trip. New component
proofs characterize the missing-left and present-left cases. A merged operand
is not classified as left-only. Existing outer-join match accounting remains
independent of WHERE. CTAS preserves star names, uses original expression spans
for explicit merged expressions, inherits left affinity, and accounts for the
coalesce expression's broader possible types in compound affinity selection.

Baseline seed **354550** records **2,676 cases / 1,476 differences**, all rejected
successful FULL shared-name statements. The expanded development corpus adds
DISTINCT, output aliases, invalid ordinal/collation controls and compounds;
seed **354551** passes **3,960 / 0**. Final-checkpoint fresh seed **354552** passes
**8,560 / 0**, with eight fixtures covering all six declared affinity classes,
empty inputs, mixed NULL/numeric/text/blob values, quoted/repeated USING names,
NATURAL, qualified and unqualified stars, windows, CTAS/INSERT SELECT and compound
metadata. The corpus mixes fixed controls with seeded data/query combinations;
it is not entirely unseen. Successful stdout, error status, C catalog/typed-row
and integrity observations, subsequent C writes, Lean reopening and conditional
main/WAL byte immutability are compared in both file modes and three page sizes.

Outer-ON regression seed **354553** passes **6,016 / 0**; wrapper regression seed
**354554** passes **11,232 / 0**. Each also passes eight immutable-image/integrity
checks. Final checks pass **354 build jobs, 278 executable tests, 1,259 headline
component proofs**, both audits, and 61 accepted reverse-file cells with two
declared unsupported. Implementation SHA-256:
`717ef68972ed18de8e92abe220f2dc72e3e2d5ee1151d34a5afaae1a1fe16415`.
Native bindings are unchanged. These results close the measured shared-column
join gap; they do not establish full SQLite SQL/file/WAL equivalence. General
joined expressions, predicate output aliases and previously recorded planner
ordering/other feature gaps remain. Reports:
`sqlite-join-full-using-*20261025.json`; combined harness:
`scripts/run-join-full-using-differential.py`.


## Joined predicate aliases and ON term binding (2026-10-25)

Two-source INNER/LEFT/RIGHT/FULL joins now resolve result aliases in WHERE and
ON using the original projection expressions. Source columns take priority,
including ambiguous and TRUE/FALSE-named columns. Substitution is non-recursive;
qualified names cannot refer to output aliases. Explicit collation, affinity,
ORDER aliases, duplicate aliases and CTAS names survive projection lowering.
Existing successful join translations remain the first execution path. Empty
inputs and LIMIT 0 still validate names and required collations.

Pinned SQLite's resolveAlias copies the result expression without EP_OuterON.
Consequently an alias replacing an entire AND-split ON term becomes a WHERE
condition; false/NULL rows can disappear instead of being null-extended. The
split ignores COLLATE and valid probability-hint shells, while unary plus and
containing comparisons retain ON status. The implementation models this observed
behavior explicitly rather than treating all alias substitutions as ordinary ON
expressions. Component proofs establish source-name priority, one-level alias
substitution, whole-term alias relocation and preservation of existing successful
join translations; they do not establish full SQLite equivalence.

Baseline seed **354560** records **2,352 cases / 1,872 differences**, all rejected
successful statements. Expanded baseline **354565** records **3,084 / 2,412**:
2,352 rejected successes, 48 incorrect successful outputs and 12 accepted C
errors. Initial development **354561** records **4,304 / 64**. All 64 differences
were incorrect outputs caused by preserving ON status on a whole-term alias;
the complete negative result and its component-check report remain available.
Corrected development **354566** passes **5,264 / 0**. Separate strict regression
replays pass **64 / 0** for those ON failures and **60 / 0** for every originally
accepted baseline mismatch. Each labelled selection retains its source hash and
the complete original report; both engines rerun on the saved fixtures, with
complete stdout also compared for errors. These are regression replays, not
fresh evaluations.

Final-checkpoint fresh seed **354562** passes **11,168 / 0**. FULL shared-column
regression seed **354563** passes **3,960 / 0**. The fresh corpus mixes fixed
controls with seeded data/query combinations across eight fixtures, all six
declared affinity classes, empty inputs, actual TRUE/FALSE source columns,
three page sizes and both file modes. The combined harness compares successful
stdout, error status, independent C catalog/typed-row/integrity observations,
follow-up C writes, Lean reopening and main/WAL immutability whenever C leaves
those bytes unchanged. It does not compare error text or partial stdout in its
both-error branch; the two saved-failure replays separately compare stdout.

Final checks pass **354 build jobs, 279 executable tests, 1,263 headline component
proofs**, both audits and 61 accepted reverse-file cells with two declared
unsupported. Implementation SHA-256:
`f18562096b53d9f47ba22aa483e1fe6e0f1f778cb3bb9fa17b63cb05f1c9961f`.
Native bindings remain unchanged. General joined expressions, compound joined
star ordering and previously recorded planner/file/WAL gaps remain. Reports:
`sqlite-join-alias-*20261025.json`; harness:
`scripts/run-join-alias-differential.py`.


## Joined compound result binding (2026-10-25)

Compound ORDER BY now binds joined source references to explicit internal
identities and expands stars in the same order as the live join projection.
USING/NATURAL suppress duplicate right slots. Star output labels bind before
source names, while qualified references retain their own source identity.
RIGHT merged stars address right values; FULL merged slots are distinct from
either qualified source and from an explicit coalesce() call. Ordinary scalar
wrappers, aliases, collation selection and result positions remain separate.
The default single-source/constant compound binding path is unchanged.

Baseline seed **354570** records **7,232 cases / 1,984 differences**: 1,788
rejected successful statements, 148 accepted C errors and 48 wrong successful
outputs. Expanded development seed **354571** passes **15,552 / 0**, including
empty inputs, stars mixed with expressions, later-arm aliases, quoted source
names, all four compound operations, CTAS/INSERT SELECT and invalid widths,
positions and collations. Final-checkpoint fresh seed **354572** passes
**31,744 / 0**, with eight fixtures covering all six declared affinity classes,
empty inputs, three page sizes and both file modes. Fixed controls are mixed
with newly seeded data/query combinations; the corpus is not entirely unseen.
The combined harness compares successful stdout, error status, independent C
catalog/typed-row/integrity observations, subsequent C writes, Lean reopening
and main/WAL immutability whenever C leaves those bytes unchanged. Its both-error
branch does not compare partial stdout or error text.

A separate strict replay of all **1,600 baseline read-only failures passes
1,600 / 0**, rerunning both engines and comparing stdout even on errors, main/WAL
immutability and C integrity checks. The labelled selection keeps its input hash
and the unfiltered baseline. Write failures are covered by the complete combined
harness. Compound-tail regression seed **354573** passes **1,812 / 0**, and
compound-collation regression seed **354574** passes **1,636 / 0**. Those older
regression harnesses compare successful stdout and error status, with immutable
main/WAL images; their both-error branch does not compare partial stdout.

Checks pass **354 build jobs, 280 executable tests, 1,266 headline component
proofs**, both audits and 61 accepted reverse-file cells with two declared
unsupported. The new component proofs separate source/merged identities and
establish that star binding preserves the live projection's operand identities
and positions. One initial unit incorrectly expected TEXT for a compound CTAS
value; pinned C established INTEGER was correct. Only that test expectation
changed, and its evidence is retained separately. Native bindings are unchanged.
Implementation SHA-256:
`e41adcbc93954901cca1934f0fb2ffbbdc4b5bd83770a25775a5b806ef01eeba`.
Reports: `sqlite-join-compound-*20261025.json`; combined harness:
`scripts/run-join-compound-differential.py`. This checkpoint does not establish
full SQLite SQL/file/WAL equivalence.

The complete fresh report exceeds GitHub's single-file size limit as plain JSON.
It is retained without filtering as
`sqlite-join-compound-fresh-20261025.json.gz`; the accompanying
`sqlite-join-compound-fresh-20261025-summary.json` records exact compressed and
uncompressed hashes, sizes, case count and executable/harness/source identities.
The archived bytes were decompressed and checked against the original report.


## General joined expressions: implementation checkpoint (2026-10-25)

Two-source joins now admit general scalar projections, computed predicates,
DISTINCT, ordering, grouping and aggregates through the existing Core expression
engines. Binding maps each physical or coalesced source operand to a separate
expression slot with its original affinity. The context is used for expression
evaluation only: it creates no stored table and allocates no synthetic rowids.
Dynamic ON evaluation records right-side matches before WHERE filtering and
preserves unmatched outer rows. Existing successful Core reads remain the
first execution path; the refinement theorem is retained for their original
scope. Subqueries and joins with more than two sources remain unsupported.

Scalar min/max/nullif now choose the first argument with any collation,
including a column's implicit BINARY collation. CTAS independently validates
its resulting column collations: a plain SELECT can legally use a later unknown
collation that still makes CREATE TABLE AS fail. Output column binding, selected
compound collation and expression evaluation retain their separate roles.

Read baseline seed **354580** records **5,904 / 5,454** differences; write baseline
**354585** records **1,040 / 848**. In-memory component drafts on 1,476 saved queries
progressed from **968** differences (including incorrect output width), to **20**,
to **8**. These are development-only component replays, not public execution,
fresh evaluation or file/WAL evidence. Their complete negative results remain.
Production development read seed **354581** passes **12,000 / 0** plus eight
immutable-fixture checks. Initial write seed **354586** records **2,272 / 64**;
all 64 accepted CTAS errors are preserved. After result-collation validation,
write development **354589** passes **2,272 / 0**, and a strict replay of all
64 saved failures passes **64 / 0** with unchanged files and error stdout.

Fresh evaluation at the final source checkpoint is mixed:

- Read seed **354582**: **24,640 cases / 2 differences**, plus 16 passing fixture
  checks. Both differences are the same empty-right LEFT JOIN search-key
  overflow in the two file modes. SQLeanite accepts a statement that C rejects;
  this remains an open bug. All failures have a separately labelled replay input.
- Write seed **354587**: **5,184 / 0**, including CTAS/INSERT SELECT, C catalog and
  typed-row observations, follow-up C writes and Lean reopening. Immutability is
  required whenever the reference leaves main/WAL bytes unchanged. This writer
  harness compares error status, but not partial stdout when both engines fail.

Both fresh corpora mix fixed controls and newly seeded data/query combinations
across eight fixtures, six affinity classes, empty inputs and three page sizes.
The read harness compares complete stdout even on errors. Regression checks pass
**2,960 / 0** scalar-collation outcomes and **648 / 0** CTAS cases. The separate strict
joined compound regression replay passes **1,600 / 0**, including complete stdout
on errors and immutable main/WAL checks. It is not a fresh evaluation.

An explicit overflow/order stress corpus still records **1,152 / 112** differences
through the public executable: C skips evaluation of some rows using WHERE and
scan/window planning while the port evaluates them too early. The earlier
in-memory draft records **576 / 56** for the same query family. Neither result is
filtered out of compatibility evidence. Planner-dependent evaluation and error
streaming remain open work, alongside the existing SQL and file/WAL gaps.

Checks pass **354 build jobs, 282 executable tests, 1,272 headline component
proofs**, both audits and 61 accepted reverse-file cells with two declared
unsupported. The new component proofs cover first-argument collation choice,
preservation of existing successful execution, read-state preservation and the
pure-ON row path; they do not establish full SQLite equivalence. Native bindings
remain unchanged. Implementation SHA-256:
`e66b4bc0df5366e57dac554a69a00ece80fa61747d2272ca4e80221a51e8873f`.
Reports: `sqlite-join-scalar-*20261025.json` and
`sqlite-join-evaluation-order-baseline-20261025.json`. Public harnesses:
`scripts/run-join-scalar-differential.py`,
`scripts/run-join-scalar-write-differential.py` and
`scripts/run-join-evaluation-order-differential.py`.


## Joined scan direction and early WHERE evaluation (2026-10-25)

General expression joins now derive left-rowid traversal from the leading ORDER
term and retain the unmatched-right suffix separately. WHERE predicates can
reduce an outer side only through a conservative source-null test adapted from
the pinned SQLite expr.c/select.c rules. Source-local WHERE terms are applied
before ON when their source survives that reduction. Ordinary functions, IS,
CASE and mixed OR expressions do not spuriously prove a non-null source.

A fully ordered rowid scan applies OFFSET before evaluating ordinary projection.
Transient non-rowid equality indexes retain a separate sorting path; RIGHT/FULL
suffixes require the final sort. Dynamic rowid lookup expressions and output
aliases are bound to their original sources before scan planning. The component
proofs establish the AND/OR structure of the conservative null test and that
reduction cannot add an outer side. They are not a proof of complete planner or
SQL equivalence. Generated source slots, schema affinity and native bindings
remain unchanged.

The public overflow/order baseline records **1,152 / 112** differences; all 112
saved failures pass a strict regression replay at this checkpoint, comparing
stdout on errors, immutable main/WAL bytes and C integrity. A preliminary
in-memory component replay passes **576 / 0**; its exact draft source is retained
as a diagnostic text artifact, outside the production source tree.

Expanded development seed **354591** records **4,800 / 214** differences: 14
successful C statements were rejected because OFFSET did not skip projection,
and 200 both-error cases lost rows emitted before the error. The complete result
is preserved. After ordered-scan window handling, a strict replay of all 214
passes the 14 status failures and retains **200 partial-output differences**.
The seven distinct successful cases have executable regressions.

Fresh final-source seed **354592** records **10,240 / 330** differences, with all
16 immutable-fixture checks passing. Error/success status agrees in every case;
328 differences are missing output before an error, and two are the same
unordered INNER JOIN row-sequence mismatch in both file modes. The latter needs
a right-driven computed-rowid lookup. No mismatches are discarded or relabelled
as passes. Fixed controls and newly seeded safe values, overflow positions and
windows are mixed across eight fixtures and three page sizes. Every fresh
failure is also retained in a labelled replay input.

A separate fresh general-expression corpus, seed **354593**, passes
**24,640 / 0** plus 16 immutable-fixture checks. Write regression seed **354594**
passes **2,272 / 0** with typed C file observations, follow-up writes and reopening.
Those successful corpora do not close the older empty-search bug: its explicit
saved control still records **2 / 2** at this checkpoint. Error-prefix streaming
and empty-input search-key evaluation remain active work.

Checks pass **354 build jobs, 283 executable tests, 1,275 headline component
proofs**, both audits and 61 accepted reverse-file cells with two declared
unsupported. Implementation SHA-256:
`e5393de5c68de27afdfff694acb6c351bcc2ef0707c31ea77c121914d910a126`.
Reports: `sqlite-join-evaluation-order-*20261025.json`; harness:
`scripts/run-join-evaluation-order-differential.py`. This is an implementation
checkpoint with documented open differences, not full SQLite compatibility.


## Joined read prefixes and shared traversal planning (2026-10-25)

Two-source, non-compound SELECTs now retain rows produced before a later
expression error. A structural joined iterator evaluates ON, WHERE, projection,
DISTINCT and the scan window in visitation order, and stops before evaluating
further rows after an error or a satisfied LIMIT. OFFSET skips ordinary
projection when DISTINCT does not require it. The iterator tracks matched right
rows before WHERE and preserves the unmatched-right suffix for RIGHT/FULL joins.
A shared traversal plan chooses the outer source for computed rowid probes and
the scan direction; materialized sorting and streaming use that same plan.

The ordinary Core SELECT API still returns its existing Except result. The new
observed read report additionally carries a successful prefix on errors; an
explicit refinement theorem proves that erasing the observation agrees with the
ordinary two-source, non-compound execution. File and WAL execution expose these
observations to the CLI and preserve the live state after failed reads. Successful
statements are observed after required publication. This buffers a prefix until
the statement completes or fails; it does not claim real-time row delivery.
Failed CTAS and INSERT SELECT retain the ordinary atomic execution path.

A development-only in-memory component replay passes **2,400 / 0**; its input
transformation and draft source hash are recorded separately. Production
regression replay of all 330 previously saved failures passes **330 / 0**,
including error stdout, and development seed **354610** passes **4,800 / 0** plus
eight immutable-fixture checks. Script-output regression seed **354613** passes
**4,392 / 0**, including partial stdout; script-error seed **354614** passes
**1,980 / 0** with typed C observations and follow-up state checks, but its
both-error branch does not compare partial stdout.

The first fresh checkpoint, source `bd447141846fc66e469e1c5b17a51b88e6a230706afd98d34631bb7dd7aa4f2c`,
records **16,128 / 6** differences at seed **354611**. All six are retained: a
right-driven computed rowid probe visited rows in the wrong order before a
bounded sort and evaluated an overflowing projection that C skipped. The shared
traversal fix passes all six in a strict saved-case replay. Five C-backed
executable controls also cover the computed lookup and unvisited source-local
WHERE conditions. The initial fresh scalar and writer corpora passed
**24,640 / 0** and **5,184 / 0**, respectively; those earlier passes are not used
as final-source evidence.

Fresh evaluation after the traversal correction, on frozen source
`56839610d77ab28c39ad61858bb2d99d556c77765b0c0b9495eb762e89bbea6c`, passes:

- Joined evaluation-order seed **354616**: **16,128 / 0**, plus 24 passing
  immutable-fixture checks. Complete stdout is compared even on errors.
- General-expression read seed **354617**: **24,640 / 0**, plus 16 passing
  immutable-fixture checks, also including error stdout.
- Joined writer seed **354618**: **5,184 / 0**, with C integrity, catalog and typed
  contents, follow-up C writes and Lean reopening. This harness compares error
  status, but not partial stdout when both executions fail.

These corpora mix fixed controls and newly seeded values, overflow positions and
windows. They exercise the public executable in ordinary-file and WAL-file modes
on C-created files at three page sizes. They are scoped evidence, not a complete
SQLite test suite. Empty-input search-key evaluation, general planner behavior,
other SELECT shapes' error prefixes and the existing file/WAL gaps remain open.

Checks pass **354 build jobs, 285 executable tests, 1,283 headline component
proofs**, both audits and 61 accepted reverse-file cells with two declared
unsupported. The component proofs cover stopped iterators, source exchange and
observation erasure, not SQLite equivalence. The first boundary audit correctly
rejected the undocumented new observer entry point; that negative result is
preserved. The entry point now has a classification tied to the refinement proof,
and its callback/cache/file IO seam is explicitly unproved. All nine native
bindings and their audit allowlist are unchanged. Reports and diagnostic source:
`sqlite-join-stream-*20261025.*`; public harnesses remain the joined read,
evaluation-order, writer and script regression harnesses listed above.


## Joined cursor initialization and empty search inputs (2026-10-25)

Joined expression execution now represents scan, rowid equality, rowid IN,
rowid-range and automatic-index lookup initialization separately. Selected
search keys are evaluated before seeking their candidate rows, including empty
inputs. A Rewind or empty automatic-index construction can instead end an inner
cursor nest before its key is evaluated. LEFT joins retain their unmatched-row
path. Search predicates use their original affinity and collation, unary plus
disqualifies a bare indexed column, and Boolean IS TRUE/FALSE does not become an
equality seek.

The shared traversal plan also represents a constant rowid cursor that opens
before the other source and handles constant IN visitation order. Range start
and end constraints follow scan direction. Automatic lookup constraints are
chosen in term order with index-affinity checks. ON name/function resolution and
code-generation admission are independent of whether a builtin value evaluator
is reached. Empty-pair adapters no longer erase computed cursor keys; ignored
non-key ON expressions still preserve their earlier behavior. A scan ordered
only by its outer rowid may emit and stop at LIMIT even when the inner cursor
uses an automatic index.

This remains a partial implementation of SQLite's planner: it does not implement
the complete cost/statistics search or general constant propagation. No C query
engine, native binding or opaque-audit expansion is used at runtime. The new
component proofs establish point-key error propagation, empty Rewind behavior
and empty automatic-index termination. The existing collation theorem keeps its
original statement; its proof is factored through a separate bound-query lemma.

The preserved initial empty-search baseline, seed **354600**, records
**5,184 / 252** differences at the earlier scalar checkpoint. Its exact original
harness is retained. An expanded baseline, seed **354601**, records
**16,800 / 1,636** at the streaming checkpoint. Both include ordinary-file and
WAL-file execution against pinned C-created databases; no failures are removed.

Initial cursor development, source
`23c51e1d8343a3124ca633b621746bc96d76ed9953509287a35bf81dd01febce`, records
**16,992 / 656** at seed **354620**. The initial focused diagnostic records
**120 / 16**, and the existing executable suite rejects an accidentally lost
empty-input JSON-function admission. These negatives are preserved, including
the source patch. The initial general read and order development corpora pass
**12,000 / 0** and **4,800 / 0**, respectively; they are not final-source checks.

After repairing RIGHT/FULL empty adapters, Boolean IS, constant cursor traversal
and ON admission, development seed **354623** passes **16,992 / 0**. All 656 saved
failures pass a strict replay, and the two older saved scalar-search failures
also pass. The focused diagnostic passes **120 / 0** and order development
passes **4,800 / 0**. These results use source
`81fb8c9e6f7967a97cab5f6fa939c7808efba6fb895a7f1c421b740b7e5ee160`.
A newly added executable control then exposes the remaining outer-only ORDER BY
case with LIMIT; that negative and its C oracle are retained separately.

Fresh evaluation at the final source checkpoint
`da7dadea628d68a8700ea2d350c8576fb7613dff6d4c83eda2fb908a7b8205ab`:

- Empty-search seed **354626**: **35,136 / 50**, plus 16 passing immutable-fixture checks.
- Joined order seed **354627**: **16,128 / 0**, plus 24 passing immutable-fixture
  checks.
- General scalar read seed **354628**: **24,640 / 0**, plus 16 passing
  immutable-fixture checks.
- Joined writer seed **354629**: **5,184 / 0**.

The 50 fresh empty-search differences are retained without filtering: 42 C
errors are accepted because a legacy RIGHT empty adapter skips ON terms after
WHERE removes the outer side; eight C successes are rejected when transitive
rowid constraints select the opposite outer cursor. Every failure also appears
in a labelled saved-case replay input. This fresh result does not establish
complete empty-search compatibility.

The read corpora compare exact stdout even on errors, success/error status,
immutable main/WAL bytes and pinned-C integrity/typed observations. The writer
corpus checks C catalog and typed contents, follow-up C writes and Lean reopening,
and requires unchanged bytes when C leaves its files unchanged; its both-error
branch does not compare partial stdout. Corpora mix fixed controls and newly
seeded values, overflow positions and windows across three page sizes. Counts
are scoped differential outcomes, not a percentage of SQLite compatibility.

Final checks pass **354 build jobs, 286 executable tests, 1,286 headline
component proofs**, both audits and 61 accepted reverse-file cells with two
explicitly unsupported. The executable suite includes 47 C-backed cursor
controls. Native bindings remain nine; native source SHA-256 is unchanged at
`cb7b0d02bd86a1c4b42621f78f94cbefb73bcf52574ce4287e985c7eddb2fa3c`.

A new, independent constant-search baseline at this same final checkpoint,
seed **354640**, records **7,328 / 252** differences: 144 C errors are accepted,
and 108 C successes are rejected. It includes empty and nonempty sources.
The next work is fixed-column propagation and inner-source WHERE filtering
before ON evaluation. This negative is retained alongside the existing SQL,
planner, file-format and concurrent-WAL gaps; this is not full SQLite
compatibility.

Reports: `sqlite-join-empty-search-*20261025.*`,
`sqlite-join-search-*20261025.*`, and
`sqlite-join-constant-search-baseline-20261025.json`. Public harnesses:
`scripts/run-join-empty-search-differential.py`,
`scripts/run-join-constant-search-differential.py` and the existing joined
read/order/write and strict saved-failure harnesses. Focused diagnostic harness
sources and intermediate production patches are retained as labelled text
artifacts outside the production source tree.

## Reduced outer cursors and rowid filter preparation (2026-10-25)

Empty-side outer-join adapters now retain WHERE planning. A WHERE condition that
removes an outer side reaches the ordinary cursor planner, where source-local ON
conditions can run before an empty inner lookup. Direct rowid equalities carry
constant range bounds to the chosen outer source, and inner WHERE ranges retain
the difference between an empty Rewind and an empty range seek. A present source
row's physical rowid cannot be NULL, so an impossible rowid IS NULL filter ends
the scan before evaluating dynamic ON expressions.

The planner also retains which columns originated on a nullable outer side.
This affects which rowid NOT NULL tests survive preparation and which cursor
is chosen. The null-rejection walk now follows pinned `expr.c`'s asymmetric AND
walk: root NOT NULL tests are peeled, left conjuncts recurse, and the final
right conjunct uses the ordinary expression walker. The earlier symmetric
component theorem has been replaced by the corrected statement; its earlier
symmetric optimizer claim is withdrawn. C-backed controls preserve the
negative examples with the two conjunction orders.

Development evidence is retained in full:

- The initial reduced-cursor implementation passes the previous **50 / 0**
  saved-case replay and records **12,992 / 300** differences at seed **354645**.
- Adding impossible-rowid filtering and inner ranges passes **300 / 6** in
  saved-case replay. Fresh seed **354646** records **27,136 / 12** plus 16 passing
  immutable-fixture checks. Every failure is the same reduced LEFT JOIN plan
  shape on different fixtures/file modes; the executable regression rejects it.
- Preserving nullable-source preparation and the NOT NULL walk passes the saved
  lists of **300 / 0**, **12 / 0**, and **50 / 0**. Expanded fresh seed **354647**
  passes **39,936 / 0** plus 16 immutable-fixture checks, but a separately expanded
  fixed control set records **170 / 12** and the executable suite still fails.
  Those twelve expose rowid ranges combined with retained or trivial NOT NULL
  tests. Both the passing fresh corpus and the negative controls are retained;
  the fresh pass alone did not close this work.

Fresh evaluation on frozen production source
`fd06ae52c1258ace0ccbb8480d5c3d19103228e47338f83cd75f5859703cac62`:

- Expanded reduced-cursor seed **354648**: **52,736 / 28**, plus 16 passing
  immutable-fixture checks.
- Joined evaluation-order seed **354649**: **16,128 / 0**, plus 24 passing
  immutable-fixture checks.
- General scalar-read seed **354650**: **24,640 / 0**, plus 16 passing
  immutable-fixture checks.
- Joined writer seed **354651**: **5,184 / 0**.

All four saved-failure lists pass strict final-source replay: **50 / 0**,
**300 / 0**, **12 / 0**, and **12 / 0**. These are regression replays, with some
overlapping inputs, not additional fresh examples.

The final expanded corpus still exposes **28 differences**: 26 C successes
are rejected and two C errors are accepted. Twenty-four involve an unordered
reduced LEFT/FULL join with a retained right NOT NULL filter, a left rowid range
and source-local ON conditions. Two involve a WHERE rowid equality and two a
reduced FULL join's empty automatic lookup. Every mismatch remains in the full
report and in an explicitly labelled saved-case replay input. This checkpoint
does not establish complete reduced-join compatibility.

The fresh corpora mix fixed templates and newly seeded values, overflowing-row
positions and scan windows. Reads compare exact stdout, including rows before
errors, success/error status, unchanged main/WAL bytes and pinned-C integrity
and typed observations. Writers compare C catalog and typed contents, follow-up
C writes and Lean reopening, with unchanged bytes whenever C leaves its files
unchanged. The writer's both-error branch does not compare partial stdout.
Ordinary-file and WAL-file modes and three C-created page sizes are included.

Checks pass **354 build jobs, 289 executable tests and 1,290 headline component
proofs**, both audits and 61 accepted reverse-file cells with two declared
unsupported. The three new executable regressions contain **188 C-backed
controls**. Component proofs cover empty-adapter guards, unchanged range-key
values and the null-walk rule; they are not proofs of full SQLite equivalence.
All nine native bindings remain unchanged, with native source SHA-256
`cb7b0d02bd86a1c4b42621f78f94cbefb73bcf52574ce4287e985c7eddb2fa3c`.

This remains a bounded two-source planning implementation, not the complete
SQLite cost/statistics planner. General constant propagation, inner-source WHERE
ordering and the previously recorded SQL/file/WAL gaps remain open. The prior
constant-search baseline retains **7,328 / 252** differences at its earlier
checkpoint. No compatibility percentage is inferred from these counts.

Reports and intermediate patches: `sqlite-join-reduced-cursor-*20261025.*`.
Public harness: `scripts/run-join-reduced-cursor-differential.py`, supplemented
by the existing joined read/order/write and strict saved-failure harnesses.
The exact earlier harness revisions are retained beside their results.

## Fixed-column preparation, singleton seeks and declared nullability (2026-10-25)

Two-source inner joins now prepare direct constant equalities with the pinned
SQLite column-affinity rules. Rightmost equalities define fixed columns, their
defining comparisons remain identifiable, and BLOB-affinity substitution is
restricted to the eligible comparison operands. Source-local inner WHERE tests
run after cursor initialization and before dynamic ON expressions. These rules
are shared by materialized and observed execution; they preserve partial output
and dynamic errors instead of only matching successful row sets.

A singleton outer seek suppresses the repeated-lookup automatic index. Original
search terms precede virtual commuted terms, whose analyzer order is reversed;
a component permutation proof shows that this ordering retains every candidate.
An unfixed singleton rowid bound can propagate across a direct rowid equality.
Fixed-column preparation and CROSS JOIN fences affect which constraint supplies
a point lookup. This remains a bounded two-source plan model, not SQLite's full
cost/statistics solver. Constant propagation is currently limited to the admitted
direct ON constraints and singleton rowid paths.

Declared NOT NULL payload columns now participate in null-test preparation,
alongside physical rowids. Original outer-source nullability is retained even
when WHERE later reduces the join. An impossible IS NULL on a guaranteed-present,
non-null column ends the scan before dynamic ON evaluation. A separate suspected
singleton-IN issue passed all eight baseline public-file controls; no production
IN change was made on that hypothesis, and positive controls are retained.

Component experiments are labelled separately: a draft passes **3,664 / 0**
constant-search comparisons and **48 / 0** affinity controls in memory. These
are not production-file or fresh seeded results. Public baseline controls record
**400 / 98** singleton/term-order differences and, at the later pre-nullability
checkpoint, **840 / 80** declared-NOT-NULL differences.

Intermediate negative results are retained:

- The first integrated implementation passes the saved constant-search replay
  **252 / 0**, but records **28 / 2** in the prior reduced-cursor replay and
  **400 / 60** singleton controls; its executable suite fails.
- Adding singleton propagation and virtual-term ordering passes those three
  lists (**252 / 0**, **28 / 0**, **400 / 0**), but a prior LEFT JOIN control
  exposes an unsound global preference for constant point keys. Its executable
  suite fails. The corrected implementation restores original point-key order
  and prepends only the eligible inherited singleton constraint.
- The corrected point selection passes 292 executable tests, then the expanded
  declared-NOT-NULL controls expose the **840 / 80** negative above. Extending
  source nullability metadata closes this focused regression.

Final-source saved-failure replays pass **252 / 0**, **28 / 0**, **98 / 0** and
**80 / 0** with exact error stdout, immutable main/WAL bytes and C integrity.
The focused public controls pass **400 / 0** and **840 / 0**. These are replay
and development results, with overlapping cases; they are not fresh examples.

Fresh evaluation on frozen production source
`bfa4c78e33b7ff26075d4158679a45b27f2b58898ee8e912bc43030bf1b53b37`:

- Fixed-column/singleton/null-metadata, seed **354660**: **44,736 / 168**, plus 16 immutable-fixture checks.
- Reduced outer cursors, seed **354661**: **52,736 / 0**, plus 16 immutable-fixture checks.
- General scalar reads, seed **354662**: **24,640 / 0**, plus 16 immutable-fixture checks.
- Evaluation order, seed **354663**: **16,128 / 0**, plus 24 immutable-fixture checks.
- Joined writers, seed **354664**: **5,184 / 0**.

The fresh checkpoint still has differences. Fixed-column/singleton/null-metadata: 96 C errors accepted, 72 C successes rejected, 0 other output/state differences. Every mismatch is retained in its full report and a labelled saved-case input.

A separate fixed-shape discovery corpus at the same checkpoint records **1,200 / 8**, plus 12 immutable-fixture checks. It varies equality orientation and the expression surrounding a fixed column, including INTEGER/TEXT/BLOB affinities and empty/nonempty inner tables. This is a focused discovery set, not a newly seeded evaluation. All results and any diagnostic C query plans are retained.

Read corpora compare exact stdout, including rows before errors, error status,
immutable main/WAL bytes and C integrity/typed observations. Writers compare
catalog and typed contents, follow-up C writes and Lean reopening; they require
unchanged bytes whenever C leaves its files unchanged. The writer's both-error
branch does not compare partial stdout. Seeded corpora mix fixed templates and
new values, overflowing-row positions and windows, in both file modes and three
C-created page sizes. Counts are not a percentage of SQLite compatibility.

Checks pass **354 build jobs, 293 executable tests, 1,294 headline component
proofs**, both audits and 61 accepted reverse-file cells with two declared
unsupported. The four new executable helpers contain **812 C-backed controls**.
The four new component claims cover unfixed lookup preservation, empty inner
filter erasure, candidate permutation and outer-source nullability; they do not
prove the general planner equivalent to SQLite. Native bindings remain nine and
native source SHA-256 remains
`cb7b0d02bd86a1c4b42621f78f94cbefb73bcf52574ce4287e985c7eddb2fa3c`.

The previously recorded SQL, planner, file-header, encoding and concurrent-WAL
gaps remain open. Reports, exact diagnostic harnesses and intermediate source
patches are retained under `sqlite-join-fixed-*`, `sqlite-join-singleton-*`,
`sqlite-join-declared-null-*` and `sqlite-join-null-range-search-*` in
`docs/validation`. The expanded public harness is
`scripts/run-join-fixed-column-differential.py`.

## Fixed WHERE constants and null-filter cursor estimates (2026-10-26)

Eligible fixed ON columns now participate in constant WHERE preparation before
either cursor starts. The same affinity restrictions used for ON substitution
apply to this early WHERE evaluation. Outer joins retain their previous
constant-WHERE path. A new component theorem proves this outer-join erasure;
it does not claim that all constant propagation matches SQLite.

Retained IS NULL and IS NOT NULL filters both affect the bounded two-source
cursor model. The planner counts eligible source-local null tests using original
source nullability. It uses their relative count to choose between singleton
outer seeks, following the unindexed-filter LogEst adjustment in pinned
`where.c:whereLoopOutputAdjust`. Row values do not influence this choice. The
prior NOT-NULL-only scan selector now also admits IS NULL filters. General cost,
statistics and transitive-constraint planning remain incomplete.

The previous **168** failures pass strict final-source replay, including exact
error stdout, unchanged main/WAL bytes and C integrity. A separate expanded set
of **324** pinned-C controls passes **648 / 0** public-file comparisons across
both modes, checking exact output/status and immutable bytes. These are saved
regressions and fixed development controls, not fresh seeded evaluation. The
324 controls are also executable regressions.

Fresh evaluation on frozen production source
`0219777efac8b6dd12fb44a6e98aff2f86774be43a30e62f4fe57a8f62924d91`:

- Expanded fixed-WHERE/null-data, seed **354670**: **63,936 / 514**, plus 16 passing immutable-fixture checks.
- Reduced outer cursors, seed **354671**: **52,736 / 0**, plus 16 passing immutable-fixture checks.
- General scalar reads, seed **354672**: **24,640 / 0**, plus 16 passing immutable-fixture checks.
- Evaluation order, seed **354673**: **16,128 / 0**, plus 24 passing immutable-fixture checks.
- Joined writers, seed **354674**: **5,184 / 0**.

The expanded corpus includes actual NULL values in nullable columns, additional
left/right null-filter orders, mixed affinities, empty sources and newly seeded
safe values and overflowing-row positions. Its **514** differences comprise
**496 C successes rejected** and **18 C errors accepted**. They expose trivial
non-null tests interacting with fixed-column substitution, outer-ON NULL
short-circuiting and additional singleton-key choices. Every mismatch is
retained in the full report and a labelled saved-case input. The earlier 168-case
replay is closed at this checkpoint; the broader null-data corpus is not.

An independent BETWEEN baseline on the same frozen source, seed **354680**,
records **13,856 / 322** plus eight passing immutable-fixture checks. It includes
constant and row expressions, searched CASE, joined range constraints,
INTEGER/TEXT/BLOB affinities and exact error prefixes. The differences include
240 C successes rejected, 50 C errors accepted and 32 output differences.
The parser currently lowers BETWEEN to two comparisons too early; searched CASE
also exposes eager Boolean conditions, and single-source reads can lose partial
output on a later error. All 322 negatives and the exact baseline harness are
retained. No BETWEEN implementation change is included in this checkpoint.

Reads compare exact stdout even on errors, success/error status, immutable
main/WAL bytes and C integrity/typed observations. Writers compare catalog and
typed contents, follow-up C writes and Lean reopening; unchanged bytes are
required whenever C leaves its files unchanged. The writer's both-error branch
does not compare partial stdout. All seeded corpora contain fixed templates as
well as newly generated values; these counts are not a compatibility percentage.

Checks pass **354 build jobs, 294 executable tests, 1,295 headline component
proofs**, both audits and 61 accepted reverse-file cells with two explicitly
unsupported. All nine native bindings and native source remain unchanged
(SHA-256 `cb7b0d02bd86a1c4b42621f78f94cbefb73bcf52574ce4287e985c7eddb2fa3c`).
The wider SQL, file-header, encoding and concurrent-WAL gaps remain open.

Reports: `sqlite-join-global-*20261026.*`,
`sqlite-between-*20261026.*`, and the diagnostic
`sqlite-join-fixed-followup-plan-oracle-20261025.json` in `docs/validation`.
Public harnesses: `scripts/run-join-fixed-where-differential.py` and
`scripts/run-between-differential.py`, alongside the existing read/order/write
and saved-failure runners. Intermediate source and exact focused harnesses are
retained outside the production source tree.

## NULL predicates and dependent singleton seeks (2026-10-26)

Outer ON conditions now test for the required truth outcome instead of
computing a complete three-valued scalar result. In a true-branch AND test,
a NULL left operand rejects the pair before evaluating the right operand.
NOT and OR retain their distinct short-circuit paths. The existing scalar
`Decision.run` and its result theorem are unchanged; the new `Decision.test`
has a component theorem for stopping a true-branch AND after left rejection.

Trivial NOT NULL tests on originally non-null columns are removed before
constant substitution can evaluate a fixed expression. Original outer-source
nullability still matters. Source-local point constraints are distinguished from
additional left filters when propagating a singleton bound. A derived right
point can replace an unconstrained scan or weaker range. Eligible dependent
inner point constraints take priority in a singleton, non-CROSS inner nest;
outer/CROSS fences and inherited transitive seeks retain their earlier order.
These remain bounded two-source planner rules, not the full SQLite optimizer.

The initial implementation records **514 / 4** in strict saved-case replay and
**754 / 4** in focused public controls. All four differences are unordered
reduced LEFT/FULL shapes where a derived point must replace a weaker range.
The initial source and negative reports are retained. Correcting that choice
passes final-source strict saved replays **514 / 0** and **168 / 0**. The
focused public controls pass **754 / 0**; their 377 underlying C controls
include 257 saved fixture/query pairs and 120 additional Boolean/NULL cases.
They are maintained in the executable suite. These counts are regression and
development results, not fresh examples.

Fresh evaluation on frozen production source
`fe4dc49c34abe96f5905a9283d79f1b887ed81817cbdd4453b848daa4c06876c`:

- Expanded fixed-WHERE/NULL data, seed **354690**: **63,936 / 0**, plus 16 passing immutable-fixture checks.
- Reduced outer cursors, seed **354691**: **52,736 / 0**, plus 16 passing immutable-fixture checks.
- General scalar reads, seed **354692**: **24,640 / 0**, plus 16 passing immutable-fixture checks.
- Evaluation order, seed **354693**: **16,128 / 0**, plus 24 passing immutable-fixture checks.
- Joined writers, seed **354694**: **5,184 / 0**.

All five scoped fresh corpora pass. Reads compare exact stdout, including rows
emitted before errors, success/error status, immutable main/WAL bytes and C
integrity/typed observations. Writers compare catalog and typed contents,
follow-up C writes and Lean reopening, and require immutable bytes whenever C
leaves its files unchanged. Their both-error branch does not compare partial
stdout. Corpora mix fixed templates and seeded NULL/safe values, overflow
positions and windows in both file modes and three C-created page sizes.
These results close this recorded NULL-data regression corpus; they do not
establish complete SQLite compatibility or a coverage percentage.

The separately recorded BETWEEN list still has **322 / 322** differences in
strict replay at this checkpoint. It remains open, alongside the other SQL,
planner, file-header, encoding and concurrent-WAL gaps. An isolated worktree is
used for the following BETWEEN changes while this source stays frozen.

Checks pass **354 build jobs, 295 executable tests, 1,296 headline component
proofs**, both audits and 61 accepted reverse-file cells with two declared
unsupported. All nine native bindings remain unchanged, with native source
SHA-256 `cb7b0d02bd86a1c4b42621f78f94cbefb73bcf52574ce4287e985c7eddb2fa3c`.

Reports, diagnostic plans, exact focused harnesses and the initial source patch:
`sqlite-join-null-data-*20261026.*`; the unchanged BETWEEN replay is
`sqlite-between-before-marker-replay-20261026.json`. Fresh evaluation reuses
`scripts/run-join-fixed-where-differential.py` and the existing reduced-cursor,
scalar, order and writer harnesses, with new seeds and no source changes during
the runs.

## BETWEEN operands and conditional branches (2026-10-26)

BETWEEN now retains one internal expression node through parsing, independent
source-token certification, scalar evaluation and SQL rendering. Its tested
operand is evaluated once; the two comparisons retain their own original
operand affinities and collations. Cursor planning can inspect virtual range
bounds without turning the source predicate into duplicated expressions.
Ordinary SQL function syntax cannot invoke the internal marker, including
quoted, uppercase and DISTINCT spellings.

Searched CASE and if/iif conditions now use branch evaluation, including the
separate true, false and NULL paths of AND, OR, NOT and BETWEEN. Simple CASE
continues to compare its saved base value. Scalar BETWEEN still evaluates both
bounds; branch BETWEEN can stop after its first comparison. Explicit collation
and probability wrappers retain the existing scalar-versus-branch distinction.
Two new component proofs preserve tested-operand failure through these helpers;
the existing static-condition equivalence claim is unchanged.

Development regressions on the final production source report **322 / 164**
for the saved baseline and **8 / 0** for the BLOB operand-orientation list.
The baseline had 322 differences before this change. The executable suite adds
259 pinned-C constant controls covering all no-FROM baseline queries, CASE/iif,
wrappers and marker-forgery attempts. These are maintained regressions, not
fresh examples. Diagnostic C plans preserve the remaining range-constraint,
join-order and original outer-operand marking differences.

Fresh evaluation froze production source
`df5a3b266c644e26d723deb54e3a8a638def9c13acc4f97778c6f49dbeb0550e`:

- BETWEEN, seed **354700**: **28,992 / 338**, plus 16 passing immutable-fixture checks.
- Fixed WHERE and NULL data, seed **354701**: **63,936 / 0**, plus 16 passing immutable-fixture checks.
- Reduced outer cursors, seed **354702**: **52,736 / 0**, plus 16 passing immutable-fixture checks.
- General scalar reads, seed **354703**: **25,152 / 0**, plus 16 passing immutable-fixture checks.
- Evaluation order, seed **354704**: **30,120 / 0**, plus 24 passing immutable-fixture checks.
- Joined writers, seed **354705**: **5,696 / 0**.

The 338 BETWEEN differences comprise 134 C successes rejected, 120 C errors
accepted, 16 successful output-order differences and 68 error-prefix
differences. Sixty of the error-prefix differences are single-source reads;
eight are joins. No no-FROM constant query differs in this fresh corpus.
All failures and original fixtures remain in the report and a standalone
regression input. This is a bounded improvement, not complete BETWEEN or
SQLite compatibility. Join planning and scalar error-prefix publication remain
open, along with the previously recorded SQL, file-header, encoding and
concurrent-WAL gaps.

Read corpora compare exact stdout even on failure, status, immutable main/WAL
bytes and pinned-C integrity/typed observations. Writers compare typed contents,
catalogs, follow-up C writes and Lean reopening; their both-error branch does
not compare partial stdout. Corpora combine fixed SQL templates with new seeded
data and windows in both public file modes and C-created 512/4096/65536-byte
pages. They do not measure an overall compatibility percentage.

Checks pass **354 build jobs, 296 executable tests, 1,298 headline component
proofs**, both audits, and 61 accepted reverse-file cells with two declared
unsupported. The same nine native bindings remain; native source SHA-256 is
`cb7b0d02bd86a1c4b42621f78f94cbefb73bcf52574ce4287e985c7eddb2fa3c`.
Reports, exact source patches, diagnostic C plans and the checks runner are
`sqlite-between-*20261026.*` in `docs/validation`. The next single-source
prefix change is developed in an isolated worktree while this source remains
unchanged throughout its final evaluation.

## Single-source scalar error prefixes (2026-10-26)

A single-table scalar read now retains rows produced before a later predicate
or projection error. Observed scans preserve DISTINCT representatives,
projection-before/after-OFFSET behavior and LIMIT stopping. Both scan functions
have component proofs that erasing the prefix on error gives the previous
ordinary scan result. Sorting and preparation failures still publish no prefix.
The ordinary filtered-read route uses this same scan implementation.

Both public file engines can publish the retained prefix once before returning
the original error. Observation requires the scalar route to reproduce the
ordinary SELECT failure; it cannot turn an unsupported query into success or
replace that failure. Direct Core queries bypass observation without executing
the read, preserving the existing file/index fast path. New observation
refinement and direct-query bypass theorems are registered. Prefixes are
buffered; failed scalar execution is reevaluated for observation. This does not
claim asynchronous row streaming or complete compound/grouped error behavior.

The new public harness baseline has **4,960 / 732** differences on the preceding
BETWEEN source. Every difference is stdout before an error; success/error
status already agreed. Strict replay at the final source passes **732 / 0**,
including byte immutability and C integrity checks for every saved case.
The maintained executable controls contain all 366 distinct saved fixture/query
pairs and 72 additional success/error boundary cases, using pinned-C quoted
outputs to retain value types. A separate script-publication test checks both
file engines, including unchanged main/WAL bytes after the failed read.

The first candidate, source
`9c9885be1cd1a92af860bd9f3acc350a42bb90452d30897ba2c633f666b86a5a`,
passed fresh seed **354711** at **11,072 / 0**, plus 16 fixture checks. Its
initial live-path audit failed because it still required the replaced scan
call. That negative check and exact source are retained. The final revision
updates the audit and adds the direct-query bypass to avoid computing ordinary
indexed reads merely to inspect their outcome.

Final evaluation freezes production source
`36ae3e81e3fde141cf10367a8ec7d280c9dfe4227c0be085ebef564a7affa9a1`:

- Single-source prefixes, seed **354712**: **11,072 / 0**, plus 16 passing immutable-fixture checks.
- Joined writers, seed **354713**: **5,696 / 0**.
- Saved BETWEEN regression replay: **338 / 278**. All 60 single-source prefix differences are closed; the 278 join-planning/order differences remain.

The two seeded evaluations use new data on a frozen source and binary. Their
fixed templates are retained across seeds. Single-source reads cover NULLs,
duplicates, six column-affinity declarations, overflow positions, aliases,
DISTINCT, sorting and windows, in both public file modes and three C-created
page sizes. Exact stdout is compared on success and error, with immutable
main/WAL bytes and C integrity/typed observations. The unchanged writer
harness's both-error branch does not compare partial stdout.

The C oracle also retains a CLI framing control: sqlite3 continues later
statements on the same input line after a runtime error even with `-bail`.
The maintained stop-on-error script comparison sends statements on separate
lines. This diagnostic is not silently included as a passing SQL result.

Checks pass **354 build jobs, 298 executable tests, 1,303 headline component
proofs**, both audits and 61 accepted reverse-file cells with two declared
unsupported. All nine native bindings and native source remain unchanged
(SHA-256 `cb7b0d02bd86a1c4b42621f78f94cbefb73bcf52574ce4287e985c7eddb2fa3c`).
This closes the recorded single-source prefix corpus, not full SQLite
compatibility. The wider SQL, planner, format and concurrent-WAL gaps remain.

Harness: `scripts/run-single-read-prefix-differential.py`. Reports, exact source
patches, quoted C controls, session receipts and checks runner:
`sqlite-single-read-prefix-*20261026.*` in `docs/validation`.

## BETWEEN cursor bounds and outer predicate branches (2026-10-26)

BETWEEN virtual range bounds now retain their shared parent when selecting a
rowid cursor. WHERE bounds precede competing ON terms; usable automatic
indexes precede range scans. Cursor initialization recognizes computed BETWEEN
bounds even for an empty opposite source. The traversal estimate distinguishes
one-sided and two-sided rowid ranges and counts local unindexed scan filters.
Outer-join constant substitution preserves the markings on BETWEEN's bound
list, matching `select.c:unsetJoinExpr`. Outer ON decisions now invoke the
scalar branch evaluator for each atomic predicate, retaining NULL and
short-circuit behavior for BETWEEN beneath logical operators.

These rules follow the pinned C source (`whereexpr.c`, `where.c`, `select.c`,
`expr.c`). They do not implement SQLite's complete cost planner. Three new
component theorems record exact virtual operand preservation, marked-bound
substitution, and the atom-callback refinement of `Decision.testWith`.
`Tests.lean` retains 385 independent quoted C controls as one executable test:
169 distinct saved failures, 54 range/reduction controls and 162 outer ON
branch, NULL and wrapper controls. Both public file modes are tested separately.

Development evidence is kept separate from final fresh evaluation:

- Published prefix baseline, production `36ae3e81…`: **770 fixed public controls / 394 differences**.
- Candidate `aa62d34b…`: **338 saved BETWEEN failures / 188 differences**.
- Candidate `5d42a579…`: **338 / 64**: 36 empty-adapter errors, 16 ordering differences and 12 automatic-index selection errors.
- Candidate `6e6e298e…`: **338 / 0**. The enlarged executable control test still failed on competing WHERE/ON bounds.
- Final candidate: **338 saved failures / 0** and **770 fixed public controls / 0**. These are regression and component-control results, not fresh examples.

An intermediate build failed while proving `Decision.testWith_scalar`.
Two comparisons were mistakenly launched before confirming that build's exit
status, so they ran the prior executable beside uncompiled source. Both
`controls-fourth` and `replay-fourth` reports explicitly record
`valid_production_evaluation: false`, the reason and the verified prior binary's
source digest. Their outputs and failed build/test logs are preserved; neither
run is counted as production evidence. The fifth build succeeded before the
final controls and fresh evaluations began.

Final source **`c28d1b547ab38d90225b4dc354b83e6e9f918a5fee4af950a9303e4a566f03fe`**
and executable **`12130e04ec6406c7da3f1ce76c83af6fe3fb40dd5707e03fb8b58d461286c8b8`**
were frozen across these fresh seeded runs (cases / differences):

| Corpus | Seed | Cases | Differences |
| --- | ---: | ---: | ---: |
| Expanded BETWEEN branches and cursors | 354720 | 63,552 | 50 |
| Fixed WHERE preparation | 354721 | 63,936 | 0 |
| Reduced outer cursors | 354722 | 52,736 | 0 |
| General joined scalar reads | 354723 | 25,152 | 4 |
| Joined ordering | 354724 | 30,120 | 0 |
| Joined writers | 354725 | 5,696 | 0 |
| Single-source error prefixes | 354726 | 11,072 | 0 |

The expanded BETWEEN corpus adds upper-bound errors under positive/negative
BETWEEN, NULL arguments, COLLATE and probability wrappers. All read corpora
compare exact stdout on success and error, status, immutable main/WAL files,
and independent C integrity/typed observations. Writer checks compare typed
persisted data, catalog/PRAGMA observations and follow-up C writes; their
both-error branch still does not compare partial stdout. New seeds supply
fresh data and randomized cases among reused fixed templates. The final
receipt records source hashes before/after each run, harness hashes and actual
exit codes; all 104 read-fixture checks pass.

The 50 new BETWEEN differences expose additional source-traversal choices and
row-local expression timing, including empty-source cases. Four scalar
mismatches are rows incorrectly streamed before an error for LEFT JOIN USING
with a two-source ORDER BY; C uses an automatic covering index and a complete
sorter. Every negative remains in the full reports and in the standalone
54-case final regression input. The checkpoint closes the previously saved
338 failures but does not close these new examples or establish full SQLite
compatibility.

Checks pass **354 build jobs, 299 executable tests, 1,306 headline component
proofs**, both audits, and **61 accepted reverse-file cells with two declared
unsupported**. All nine native bindings remain unchanged; native SHA-256 is
`cb7b0d02bd86a1c4b42621f78f94cbefb73bcf52574ce4287e985c7eddb2fa3c`.
The concurrent-WAL host-lock approval and broader SQL/file-format gaps remain.

Harnesses: `scripts/run-between-differential.py` and
`scripts/run-read-controls.py`. Exact source patches, all intermediate
negatives, invalid-run annotations, C controls/plans, final reports and logs
are retained as `sqlite-between-planner-*20261026.*` under `docs/validation`.

## Transactional user_version and application_id (2026-10-26)

The public Core engines now read and write `PRAGMA user_version` and
`PRAGMA application_id`, including explicit main/temp qualifiers and SQLite's
signed 32-bit prefix conversion. The pure state carries application header
words independently of table contents. BEGIN/COMMIT/ROLLBACK and named
savepoints retain their main and temporary metadata snapshots. Temporary
values reset when the connection closes and do not require a persistent write.

A metadata change is published together with table changes through the existing
rollback-journal/full-image or WAL commit path. It cannot be discarded by a
row-only no-op comparison or a cached wide-tree INSERT result. WAL reopening
decodes metadata and rows from the same recovered page-one overlay; checkpoint
and foreign-page-size conversion retain the committed words. The alias shared
with the existing freelist layout preserves its prior header/geometry proofs.
Seven additional component theorems cover signed bounds, read/set projection,
temporary-schema isolation, read-state preservation, unchanged tables and
rollback metadata restoration. They are not a full file-conformance proof.

The pinned C component oracle contains **51 scalar/initialized-transaction
controls**. Two executable tests retain those controls and journal/WAL commit,
savepoint rollback, reopening, byte immutability and checkpoint cases.

Development baseline: source `c28d1b54…`, **900 complete cases / 900 differences**.
Initial implementation `51d6401f…`: **900 / 84** using the identical generated
inputs. Exact initial source and harness are reconstructed with their report
hashes verified; all negative results remain available. The final harness keeps
every cold case and adds explicit `SELECT 1` initialization variants plus
schema/DML controls. It never inserts an invisible warm-up statement.

Final production **`3be8760f8778355a4bb2e02b623623f67d426a9a7d8018d20e1a5a17e3ef9391`**
was frozen before fresh evaluation:

- Header/snapshot corpus, seed **354731**, eight page sizes from 512 through 65,536: **6,192 cases / 936 differences**.
- Within that complete corpus, all **2,352 explicitly initialized savepoint cases match**. All 936 differences occur in 39 cold-savepoint scripts, repeated over eight geometries and three file/snapshot routes.
- Joined writer corpus, seed **354732**: **5,696 / 0**.

The header harness compares complete stdout including failed-script prefixes,
status, independent C header/integrity/typed-row reads, reopening, follow-up C
writes and unchanged main/WAL bytes whenever the reference leaves them
unchanged. C-created uncheckpointed WAL fixtures are copied only after their
transaction commits while the producer connection remains open; comparisons
use separate closed snapshots. Tests cover both public file modes for main
files and the WAL mode for overlays. Page geometry is recorded, not asserted
equal, because the existing writer can convert foreign pages to 4096 bytes.
The joined writer's both-error branch still does not compare partial stdout.
Seeds change data among reused templates; these are not all unseen SQL forms.

The remaining differences expose a pinned-C cold-connection behavior, not a
passing compatibility exception. Independently of SQLeanite, this sequence on
an existing file reproduces the loss of its visible schema and header words:
`SAVEPOINT x; PRAGMA user_version=2; ROLLBACK TO x; RELEASE x;`.
A preceding `SELECT 1` or header read avoids it; full ROLLBACK also preserves
the original database. The C-only diagnostic retains exact SQL, statuses,
outputs and subsequent reopen results. SQLeanite eagerly loads the existing
database and preserves it in these cases. **All 936 differences remain counted**
and saved in the final regression input; this checkpoint does not claim full
SQLite transaction compatibility or reproduce that data-loss behavior.

Checks pass **358 build jobs, 301 executable tests, 1,313 headline component
proofs**, both audits, and **61 accepted reverse-file cells plus two declared
unsupported**. The first live-path audit still expected the former exact
metadata-preservation call; its failure/log is retained. Updating that guard
for the explicit metadata override made the audit pass without changing the
already-evaluated production source. Native code and all nine host bindings
remain unchanged (`cb7b0d02bd86a1c4b42621f78f94cbefb73bcf52574ce4287e985c7eddb2fa3c`).
Concurrent SQLite/SQLeanite WAL locking and the other SQL/format gaps remain.

Harness: `scripts/run-application-header-differential.py`. Full cases, initial
negatives/source/harness, C-only diagnostics, component controls, session
receipts, source patch and logs are retained under `docs/validation` with the
`sqlite-application-header-*` and `sqlite-application-header-meta-*` prefixes.

## Joined range roots and USING affinity (2026-10-26)

Two-source cursor planning now accounts for rowid probes introduced by USING
and NATURAL joins. A usable transient index must have a declared affinity
compatible with the comparison. If only the left side is eligible, inner joins
scan the right source and probe the left, for both simple projections and scalar
expressions. Outer/CROSS fences remain part of that planning decision. A shared
rowid equality remains a point probe even when other shared columns also exist.

An unbounded leading-left-rowid ORDER BY can retain the left traversal despite
a dependent ON range. An independent right range can supply an ordered outer
cursor for a leading-right-rowid ORDER BY; constant ON bounds participate after
the existing WHERE bounds. Unordered two-sided right WHERE ranges use the
right-only residual condition to choose the root. A range by itself does not
override a competing left predicate or automatic equality index. These rules
use SQL structure and declared metadata, not observed row values.

The implementation retains **733 quoted C component controls** in two executable
tests, including all 187 distinct new failure inputs and 48 separate mixed-
affinity planner controls. One additional theorem states that absent shared
columns cannot supply a USING index. These are component results, not a proof
of the complete SQLite cost solver.

Development evidence is retained in full:

- Baseline 3be8760f, targeted seed 354740: **4,272 cases / 24 differences**.
- Initial 51222aee repaired the old 54 differences, but the older 338-case replay and 770-case control set each found **36 differences**.
- d85add32 passed the old 54 and 338 replays, but expanded controls found **24 / 996 differences**. Shared rowid probes fixed those; subsequent tests caught an overbroad one-sided range and a file-only PRAGMA accidentally included in a pure unit setup. Failed logs and source snapshots remain.
- First fresh candidate 9841ede6 passed 302 tests and audits, yet **250,888 fresh comparison cases contained 374 differences**: 28 in the targeted corpus and 346 in BETWEEN. Replaying those same 374 on the published baseline left only 20 differences, establishing **354 introduced regressions**. None were discarded.
- Tightening range eligibility and checking index affinity reduced that replay to **374 / 2** at f41673ed. Routing the affected simple projections through the same cursor planner removed the remaining two.
- Two harness invocations failed before producing valid measurements: an overwritten Python digest variable and an incompatible fixture input format. Their logs are retained and they are not counted as implementation evaluations.

Final frozen production source:
**a33fe5477e28ef4acd2b145597be9f3fd8f3c9751be20d586200db1d4cd83991**.

| Final fresh corpus | Seed | Complete cases | Differences |
|---|---:|---:|---:|
| Rowid ranges and USING/NATURAL | 354761 | 15,312 | 0 |
| BETWEEN | 354762 | 63,552 | 0 |
| Fixed WHERE | 354763 | 63,936 | 0 |
| Reduced outer cursors | 354764 | 52,736 | 0 |
| Joined scalar expressions | 354765 | 25,152 | 0 |
| Join ordering | 354766 | 30,120 | 0 |
| Joined writes | 354767 | 5,696 | 0 |
| Total | | **256,504** | **0** |

The fresh corpora mix new seeded values/variants with maintained SQL templates.
Read comparisons include full stdout, error prefixes, success/error status,
immutable main/WAL bytes and independent C integrity/typed-row observations.
They do not require identical diagnostic wording. Writer cases include C
reopening and integrity observations; the older writer harness's both-error
branch still does not compare partial stdout. All 112 read fixture/mode
observations match. Both public file modes and all eight SQLite page sizes are
exercised; mixed-affinity targeted fixtures also use declared rowid aliases.
Fixed replays separately pass **374, 338 and 54** cases, and fixed control
matrices separately pass **996 and 470** cases.

Final checks pass **358 build jobs, 303 executable tests, 1,314 headline component
proofs**, both audits and **61 accepted reverse-file cells plus two declared
unsupported**. All nine native bindings are unchanged. This closes the recorded
range/USING regressions; it does not establish all SQL or file-format behavior.
The 936 previously recorded cold-header-savepoint differences, concurrent WAL
locking approval blocker and other declared compatibility gaps remain open.

Source patches, every negative, C-only plans/oracles, complete reports, build/
test logs and actual runner receipts use the sqlite-join-range-followup prefix
under docs/validation. The new harness is
[scripts/run-join-range-differential.py](../scripts/run-join-range-differential.py).

## JSON validity, JSON5 and JSONB (2026-10-26)

The public Core scalar evaluator now implements json_valid(X) and
json_valid(X, FLAGS) in Lean. The byte parser handles strict JSON and SQLite's
JSON5 extensions, NUL termination, unquoted-label fallback, numeric forms,
Unicode whitespace, escapes, and the 1,000-container depth boundary. The
JSONB parser handles all node kinds and length-header widths, nonminimal
headers, superficial versus recursive admission, malformed payloads and the
ambiguous text/BLOB fallback. All masks 1 through 15 are supported; coerced
out-of-range masks fail before the NULL-input shortcut.

Malformed calls are rejected during expression preparation, including dead
branches, LIMIT 0, ignored aggregate ordering and rewritten singleton IN
expressions. Diagnostics retain the original function spelling. This adds
840 quoted C value controls and 23 exact-message controls in two executable
tests. Four validation lemmas and one recursive-admission lemma are component
proofs; they are not a proof of complete SQLite JSON compatibility.

Development evidence remains available:

- The published baseline differed in 3,460 of 3,600 initial cases; the first candidate differed in zero. That harness compared stdout/status only, so 140 error cases could match unsupported-function errors. Its source/harness snapshots and complete reports are preserved.
- Adding normalized first-line diagnostic comparison passed 3,616 cases on the second candidate. Separate component controls passed 263,172 short-byte comparisons, 432 writer cases and 40,000 upstream-generator cases. These are development results.
- Additional spelling/aggregate diagnostics found 14 differences in 21 controls. Preparation-time validation fixed these. After merging the separately validated join checkpoint, three of 26 diagnostics exposed insufficient recursion fuel after IN rewriting. Measuring the prepared expression's height repaired those failures; the negative report and pre-fix source remain.
- Initial component compilation failed on reserved Lean identifiers. Its failed log is retained; no executable evaluation is attributed to that failed build.

Final frozen production source:
**680cd7762ffcc31bb2d172a489f3efe0ea96ae7aa4a068c6b117c3e36baa3dc9**.

| Final fresh corpus | Complete cases | Differences |
|---|---:|---:|
| read | 23808 | 0 |
| writer | 1632 | 0 |
| joined-range | 15312 | 0 |
| joined-scalar | 25152 | 0 |
| joined-writer | 5696 | 0 |
| upstream-fresh | 16384 | 0 |
| Total fresh | **87984** | **0** |

The fresh read/writer seeds are 354771/354772; joined regression seeds are
354774 through 354776. The upstream-generator corpus uses seeds 3547800 through
3549847, four text/JSONB representations per seed and both file modes. Fresh
means newly seeded values/variants; SQL templates and fixed grammar controls
are also present. Independently, the fixed exhaustive corpus enumerates all
65,793 byte strings of lengths 0, 1 and 2 on both public modes and 512/65,536-byte
pages: **263,172 input-row comparisons / zero differences**. It is a fixed
component corpus, not fresh examples. Each row checks the default and all 15
masks; the exhaustive corpus also checks TEXT conversion.

JSON comparisons check full stdout, success/error status and normalized first
diagnostic lines, removing CLI prefixes and caret/source displays only. Read
observations retain immutable main/WAL bytes, independent C integrity and
typed rows. Writer observations include C reopen, catalog/typed rows, Lean
reopen, a subsequent C write, and unchanged-file checks when C changes no bytes.
The existing joined-writer harness retains its older both-error comparison
limitation. All eight page sizes are represented in the read/writer matrices;
writer page-size conversion remains separately recorded, not claimed fixed.

SQLite's pinned ext/misc/randomjson.c is compiled only as an external oracle
fixture generator. Its source/library hashes and generated inputs are saved.
The production implementation invokes no C JSON implementation and adds no
host bindings. These generator cases are not the complete upstream Tcl suite.

Final checks pass **360 build jobs, 305 executable tests, 1,319 headline
component proofs**, both audits, and **61 accepted reverse-file cells plus two
declared unsupported**. All nine native bindings and native source are unchanged.
Other JSON functions, the previously recorded 936 cold-header-savepoint
differences, concurrent WAL locking approval blocker and other SQL/format gaps
remain open. This checkpoint does not establish 100% compatibility.

All reports, source/harness snapshots, negative diagnostics and actual build/
runner logs use the sqlite-json-valid prefix under docs/validation. Large JSON
reports are losslessly gzip-compressed; the compression manifest records both
original and stored sizes/hashes. Receipt report hashes refer to decompressed
payloads. The four run-json-valid-* scripts reproduce the respective corpora.

## JSON type, array length and path lookup (2026-10-26)

The public Core scalar evaluator now implements json_type(X[,PATH]) and
json_array_length(X[,PATH]) in Lean. JSON/JSON5 text is converted to an internal
node representation for navigation; external JSONB retains SQLite's superficial
admission and operation-local validation. The implementation supports quoted and
unquoted property labels, escaped label comparison, duplicate labels, array
indices, reverse indices, NUL termination, missing-path NULL, and depth errors.
Malformed binary children follow the selected operation's behavior rather than
being rejected by a stronger global check. The internal text representation is
not an exported JSONB encoder and no JSON construction/subtype support is claimed.

Paths can contain malformed UTF-8. Byte diagnostics now travel losslessly through
the existing Except String boundary in a reserved NUL-led hex envelope when
necessary; Main writes the original bytes to stderr. Ordinary UTF-8 errors stay
plain strings. This is a generic message transport, with no SQL/result rewriting
or oracle access. Internal callers needing raw diagnostics use Diagnostic.bytes.
Quoted missing-column diagnostics preserve the quoted-token spelling, and name
validation follows the existing parser folding rules.

Identical UPDATE payloads now skip publication when assignments affect neither
rowid nor an indexed column and logical database contents are unchanged.
Indexed-column and rowid assignments retain structural writes. SQL result rows
and reported change counts are unaffected. This is shared by both file engines.

The maintained component regressions include **5,343 pinned C JSON/path controls**,
**39 additional binary-escape regressions**,
**65,536 two-byte diagnostic roundtrips**, and **24 C identical-UPDATE controls**.
Five JSON access lemmas, three diagnostic branch lemmas, one publication lemma,
one preparation-order lemma and one shared-escape lemma are component proofs. They do not establish the
complete SQLite parser, encoding or persistence specification.

Development evidence is retained:

- An initial interpreter component comparison appeared to differ in 2,595 of 5,343 cases because its C command-line error prefix was not normalized. Correcting only that normalization on the saved raw responses left zero differences; both reports and the initial harness remain. This was not production execution.
- The first successfully built production candidate passed 306 tests, but **2,236 read cases had 28 differences** (24 malformed-UTF-8 diagnostics and four missing-column diagnostics), and **424 writer cases had 16 differences** from unnecessary publication of identical payloads. Its separate 3,712-case json_valid regression passed.
- The second production candidate repaired all those differences and passed 768 no-op and 8,192 upstream-generator cases. A maintained quoted-name test then exposed validation before constant folding: SELECT 0 AND "missing" must remain zero. Its failed test log and source snapshot are retained.
- Correcting the preparation order passes the expanded 2,256 read replay, 424 writer replay, 768 no-op controls, and the complete project tests. These replays are development/regression evidence, not fresh holdout results.
- Failed builds remain in the logs: a missing explicit Except bind simplification, a compiler recursion limit from one 5,343-element test literal (split into nine declarations without dropping cases), and a test indexing a Statement array with an unavailable Inhabited instance. No measurements are attributed to those failed complete builds.

Reference inspection after the earlier candidate's 119,280 fresh comparisons
had passed still found missing JSONB escape behavior. An 18-case diagnostic
found six differences; a full byte/continuation/header/container expansion found
**156 differing rows among 103,008 comparisons**, plus four failed run-level
comparisons. These represent 39 distinct input blobs, all added to unit tests.
SQLite accepts a NUL byte immediately after backslash in its binary string
validation, while its JSON5 decoder treats decoded U+99999 as the reserved invalid
character after line continuation. A shared bounded decoder now serves validation
and label lookup, and the strict binary standard-escape list includes NUL. Text
JSON string admission is unchanged. The expanded corpus passes after repair.
Those earlier fresh and negative reports remain; only the new final source below
supports this checkpoint's final claims.

Final frozen production source:
**12a69f4738a4aae576951656f038b4c27df0e68eff69bf4946fc002677ef0b06**.

| Final fresh corpus | Complete cases | Differences |
|---|---:|---:|
| read-fresh | 27264 | 0 |
| writer-fresh | 2976 | 0 |
| noop-fresh | 768 | 0 |
| upstream-fresh | 32768 | 0 |
| valid-fresh | 9344 | 0 |
| joined-range-fresh | 15312 | 0 |
| joined-scalar-fresh | 25152 | 0 |
| joined-writer-fresh | 5696 | 0 |
| Seeded binary escape payloads | 3072 | 0 |
| Total fresh | **122352** | **0** |

New read/write seeds are 354841/354842; no-op seed 354843; JSON-validity regression
seed 354844; joined regression seeds 354845 through 354847. Fresh corpora mix
new seeded data/variants with maintained templates and fixed controls. The final
upstream corpus uses **3560000 through 3564095**, four representations per seed,
both modes and seven root/property/array paths per function. An earlier intended
final run reused 884 development seeds; it was retained and replaced with disjoint
3555000..3559095 seeds at that earlier source. Both earlier runs are development
evidence for this checkpoint, and neither enters the current final total. The
seed-audit receipt records the earlier overlap and replacement. The pinned C
extension generates oracle fixture data only; production performs no C JSON calls.
This is not a run of the complete upstream Tcl suite.

The final expanded escape corpus (seed 354848) separately passes **101,472 fixed
input-row comparisons** and **3,072 newly seeded input-row comparisons**, with
all four run-level observations also matching. Each row checks all masks/default;
root type/length are explicitly conditional SQL expressions guarded by each
implementation's own superficial check. There is no oracle-outcome filtering.
The fixed portion is excluded from the fresh total.

JSON read comparisons include full stdout, status and normalized first diagnostic
lines, immutable main/WAL bytes, and C typed-row/integrity observations. Writer
comparisons include those outputs, typed state/catalog, C and Lean reopening,
subsequent C writes, and unchanged-byte checks when C leaves its input unchanged.
The no-op corpus separately compares changed/unchanged physical publication for
both modes, all eight page sizes, five declared affinities and varied indexes.
The older joined-writer both-error comparison limitation remains. Page-size
conversion on actual writes is recorded separately and remains unresolved.

Final checks pass **366 build jobs, 309 executable tests, 1,330 headline component
proofs**, both audits, and **61 accepted reverse-file cells plus two declared
unsupported**. The native source and all nine host bindings are unchanged.
Other JSON functions, the earlier 936 cold-header-savepoint differences,
concurrent WAL locking approval blocker and other SQL/file-format gaps remain.
This checkpoint does not establish 100% compatibility.

Artifacts, full negatives, source/harness snapshots and runner/build logs use
the sqlite-json-access prefix under docs/validation. Large reports are losslessly
gzip-compressed, with original and stored hashes in the compression manifest;
runner report hashes name the decompressed payloads. The run-json-access-* harnesses,
run-json-escape-differential.py and run-update-noop-differential.py harnesses reproduce the relevant comparisons.

## JSON error positions (2026-10-26)

The public Core scalar evaluator now implements `json_error_position(X)` in
Lean. JSON5 text reports a character position; admitted external JSONB reports
a byte position. The text parser retains the reference parser's error register
across successful subexpressions, including the state used for trailing-input
errors. NULL, numeric coercion, malformed UTF-8, truncated headers, binary
payloads, object key/value parity, and nesting limits use the pinned 3.53.4
behavior. Function arity is validated before execution, preserving the original
name spelling. Production never delegates JSON work to C or an external parser.

Final frozen source: **1105732f53423719c9df52549c95dcb51664c08d5553d571f11d53eb7f537c02**.

| Final fresh corpus | Complete cases | Differences |
|---|---:|---:|
| read-fresh | 26336 | 0 |
| writer-fresh | 1952 | 0 |
| upstream-fresh | 65536 | 0 |
| access-read-fresh | 27264 | 0 |
| access-writer-fresh | 2976 | 0 |
| valid-fresh | 23808 | 0 |
| joined-range-fresh | 15312 | 0 |
| joined-scalar-fresh | 25152 | 0 |
| joined-writer-fresh | 5696 | 0 |
| Total | **194032** | **0** |

Read/write seeds are 354871/354872, related JSON regression seeds 354873 through
354875, and joined regression seeds 354876 through 354878. These corpora use
new seeded documents/mutations and values with maintained SQL templates and
fixed syntax controls. The upstream generator uses disjoint seeds **3570000
through 3574095**, four original representations plus one unfiltered byte
mutation per representation, in both public modes. Its C extension only creates
oracle fixtures. This is not the complete upstream Tcl suite.

Separate fixed-domain evidence passes **263,172 row comparisons**: all 65,793
byte strings of length zero through two, tested as BLOB and TEXT in each row,
in both modes at 512- and 65,536-byte page sizes. The maintained component replay
and development data pass **56,610 read comparisons**, **232 writer comparisons**
and **16,384 upstream/mutation comparisons**. None enters the fresh total.
The standalone interpreter component passed **27,427 controls** before public
integration; **1,675** text, storage, mutation and binary controls are maintained
in the executable unit tests. Its accidentally repeated early harness run is
retained and explicitly excluded from final metrics. A subsequent attempt to
read a concurrently compressed input report failed before evaluation; the
corrected component harness reads the lossless gzip artifact.

Comparisons cover complete stdout, exit status, normalized first diagnostic,
immutable read files, typed rows/catalog and independent C integrity checks.
Writer checks also cover RETURNING, rollback/savepoints, atomic expression
errors, C/Lean reopen, a subsequent C write and preservation of unchanged files.
The existing page-size conversion on writes is still recorded separately.

The complete build passes **368 jobs**, with **310 executable tests**, **1,335
headline component proofs**, both audits, and **61 accepted reverse-file cells
plus two declared unsupported**. Five new proofs cover diagnostic branches and
complete-input success; they are not an equivalence proof for SQLite's parser.
The native source and nine host bindings are unchanged. Other JSON functions,
the earlier 936 cold-savepoint differences, the pending concurrent-WAL locking
approval and other SQL/file-format gaps remain; this is not 100% compatibility.

Artifacts, source/harness snapshots and logs use `sqlite-json-position-*` under
`docs/validation`; four `scripts/run-json-position-*` harnesses reproduce the
measurements. Large reports are losslessly compressed with both payload and
stored hashes. Runner hashes refer to decompressed report contents.

## Ordinary percentile aggregates and shared accumulator order (2026-10-26)

The public Core paths implement `median`, `percentile`, `percentile_cont` and
`percentile_disc` as pure Lean accumulators, including NULL/type checks,
fraction validation and row-to-row tolerance, DISTINCT, FILTER and internal
ORDER BY. Aggregate steps now run across all functions for each input row.
Ordered aggregates retain evaluated arguments and defer their steps until
finalization; scalar argument errors still occur during the scan. Single-table
ordered grouped reads preserve rows emitted before a later group fails.
Aggregate misuse in scalar contexts has the pinned diagnostic.

Final frozen source: **bddf2f6ee6f9acaf6f07b8219adf02323bde6ab19c98c0d82ea2d5aea423e545**.

| Final fresh strict corpus | Complete cases | Differences |
|---|---:|---:|
| read | 14304 | 0 |
| writer | 3008 | 0 |
| Total | **17312** | **0** |

Seeds **354921/354922** generate new values and query variants at all eight
page sizes in both public file modes. Maintained templates and fixed syntax
controls recur. Strict comparisons include full output, status and normalized
first diagnostic. Reads preserve input bytes; writes check typed rows/catalog,
C integrity, Lean reopen, transaction outcomes and a subsequent independent C
write. Existing conversion to 4096-byte write pages is recorded separately.

Eleven maintained aggregate regression suites pass **11418 queries** with
fresh seeds **354923 through 354933**. Their historical success/error comparison
is weaker than the strict percentile suites: error wording and partial output
on failures are not generally compared. These are reported separately. The
development replay passes **1,340 read** and **432 writer** cases, plus **9690**
legacy regression queries. No development result enters the fresh totals.

The first standalone component had **8 differences in 1,680 cases** because
separate multiply/add rounded differently from the pinned AArch64 C binary's
`fmadd`. The implementation uses Lean's existing `Float.fma`; the component
replay passes all 1,680 controls. This fixes the tested binary's rounding and
does not establish identical results for every C compiler/architecture.
The first public candidate had **24 read and 4 writer differences**: grouped
output prefixes, interleaved error priority, and nested/scalar aggregate misuse.
All distinct failures are retained in **13 executable regression controls**;
the original negative reports and source/harness snapshots remain available.
Two local Lean compile errors are retained in development logs as well.

The complete build passes **370 jobs**, all **312 executable tests**, **1,341
headline component proofs**, both required audits, and the reverse-file matrix
(**61 accepted, two declared unsupported**). Six new proofs cover accumulator
branches and empty/limit behavior; the result-length proof follows the new
scheduler. These are component properties,
not a proof of SQLite equivalence. Native source and all nine host bindings are
unchanged. Window functions, streaming predicate/group scheduling outside these
paths, the prior cold-savepoint differences, concurrent WAL coordination and
other documented SQL/file gaps remain. This is not 100% compatibility.

Reproduction harnesses are `scripts/run-percentile-differential.py` and
`scripts/run-percentile-write-differential.py`; plans, logs, source snapshots and
comparison results use `sqlite-percentile-*` under `docs/validation`. Large
reports are losslessly compressed; receipt hashes refer to their payloads.

## Aggregate predicate and joined cursor scheduling (2026-10-26)

Ungrouped aggregation now evaluates WHERE and steps all accumulators for each
accepted input row. The retained input sequence still supplies SQLite's bare
column/MIN/MAX representative rule. Joined aggregates now use the existing
streaming join cursors, including ON conditions, early predicates, unmatched
outer rows and empty joins. Input errors stop the cursor before finalization;
HAVING and OFFSET remain after finalization. Grouped sorts retain their
evaluation order and joined grouped reads now
preserve output rows emitted before a later group fails.

Final frozen source: **cd5e711f3d6dcc090559a88374b28a66f8e8a8b4f82dd57ac6d8ef3d3a86c8ec**.

| Final fresh strict corpus | Complete cases | Differences |
|---|---:|---:|
| predicate | 18592 | 0 |
| percentile-read | 11744 | 0 |
| percentile-writer | 2240 | 0 |
| Total | **32576** | **0** |

Seeds **354951 through 354953** use fresh generated values and failure positions
with maintained templates and fixed syntax controls, across all eight page
sizes and both public modes. Strict comparisons cover full output, status,
normalized first diagnostic, immutable reads, post-write typed rows/catalog,
C integrity, Lean reopen and a subsequent C write. Write page-size conversion
is recorded separately. The predicate corpus includes dynamic ON expressions,
all four join kinds, empty/unmatched joins, deferred ordered accumulators,
FILTER, grouping, LIMIT/OFFSET, and atomic INSERT SELECT failures.

Separate maintained regressions pass **6048 queries** for numeric aggregates,
FILTER, HAVING and result tails (seeds **354954 through 354957**) and **9728
joined-output cases** for evaluation order (seed **354958**). These retain each
harness's historical comparison criterion:
legacy suites generally compare successful output and rejection, while joined
suites also retain partial output on errors; exact diagnostic comparison is
only claimed for the strict corpora above.

A broader eight-fixture empty-ON exploration at seed **354959** has **88
failures in 8,320 cases**: 68 involve unsupported `random()` and 20 involve
unsupported `json_extract()`. An isolated complete build of the published parent
**ccde0f4** (local equivalent **e75a572**) reproduces all 88; all 8,320 Lean
outcomes match the candidate.
These are retained compatibility gaps, not passing cases, and the overall fresh
runner correctly exits **1**. The parent replay is a diagnostic comparison and
is excluded from fresh success counts. The `random()` ON controls do not establish
random-number distribution or exact random output compatibility.

The initial 180-case probe retained **24 differences**, represented by **eight
distinct unit controls**. Its exit status was always zero, so its printed
failure count is used. The first implementation fixed the single-table cases
but exposed **68 joined differences in 2,440 cases**. Of these, 66 concerned
early join predicates evaluated during complete materialization; streaming
aggregate steps fixed them. The other two were the same grouped prefix loss
in both modes and remained in the expanded 3,592-case second candidate. The
materialized group route now carries its output observation. **26 joined
regression controls** and a separate emitted-prefix control preserve these
failures. The original reports, source and harness snapshots remain available.
A stale live-path guard failed after rerouting and was updated to check the
new production path. Local proof and regression-test elaboration failures,
an audit attempted
before the rebuilt CoreSQL object existed, and a corrected shell prefix in
initial unit expectations are retained as development records.

The final full build passes **370 jobs**, all **315 executable tests**, **1,344
headline component proofs**, both audits, and the reverse-file matrix (**61
accepted and two declared unsupported**). Three new component proofs cover
rejected predicate rows, predicate errors and propagation of a recorded joined
input error; sized accumulator arrays retain their length witnesses. They do
not prove equivalence to the whole SQLite planner. Native source and nine host
bindings are unchanged. Indexed streaming GROUP BY, window functions, previous
cold-savepoint differences, concurrent WAL locking
and other documented gaps remain outside this checkpoint.

The new harness is `scripts/run-aggregate-predicate-differential.py`; plans,
comparison results and logs use `sqlite-aggregate-predicate-*` in
`docs/validation`. Large reports are losslessly compressed; runner hashes refer
to decompressed payloads.

## JSONB byte encoding and public SQL integration (2026-10-26)

`jsonb()` now uses a pure Lean byte encoder. It retains JSON/JSON5 numeric
spelling and escape classes, removes the text syntax, emits minimal length
headers, and returns the encoded BLOB. Admitted input JSONB is returned byte
for byte after SQLite's shallow check; malformed descendants are not silently
validated or repaired. SQL NULL remains NULL. Function admission reports exact
argument-count diagnostics, including dead branches and zero-row statements.
No C binding, native dependency or runtime oracle was added.

Final frozen implementation: **472b7d72a2cd81709918ef4bbdd43ead3b6ee43f8319529e50e821d3f759605d**.

| Final fresh JSONB corpus | Complete cases | Differences |
|---|---:|---:|
| read | 28016 | 0 |
| writer | 1664 | 0 |
| upstream | 16384 | 0 |
| Total | **46064** | **0** |

The read and writer seeds are **354981 and 354982** across eight page sizes
and both public file modes. Newly generated values and unfiltered mutations
reuse maintained SQL templates and fixed controls. Read comparisons include
exact BLOB hex, idempotent encoding, strict binary validity, separate composition
with type/length/error-position functions, error prefixes, arity and 999/1000/1001
nesting boundaries. Independent per-input queries ensure later expressions
cannot hide an encoding difference. Writes compare output, diagnostics, typed
rows, schema shape, integrity, reopen and a subsequent C write; page-size
conversion is recorded separately.

The upstream-generator corpus uses fresh seeds **3580000 through 3581023**:
JSON and JSON5 text, C-produced JSONB of each, and an unfiltered mutation of
every representation. Every input runs separately in both public modes,
including malformed values. Only the reference process loads SQLite's
`randomjson.c` generator; production evaluates through Core. All read suites
also require unchanged main/WAL bytes and independent C integrity observations.

Separate JSON access, diagnostic-position and validity regressions pass
**39008 cases** at seeds **354984 through 354986**. These are reported apart
from the new JSONB corpora. A standalone interpreter comparison passed
**6,037 component cases** before public integration; **975 selected component
controls** remain in executable tests. Selection used input groups, size bounds
and fixed indices, not passing outcomes. Component results are not final public
coverage.

The initial public candidate had **130 differences in 674 read cases** and
**eight differences in 224 writer cases**, all argument-count diagnostics.
The admission fix is maintained by **67 distinct regression controls**. The
expanded development replay then passed **1,198 read cases** and **224 writer
cases**. Earlier component and proof elaboration failures are retained with
their corrections; negative production reports are not overwritten.

A stricter storage corpus also compares the exact `sqlite_schema.sql` text.
Its fresh seed **354983** has **64 differences in 80 cases**, so the overall
final runner exits **1**. Large JSONB bytes, row contents, integrity, Lean reopen
and subsequent C writes agree, but full-image publication regenerates the SQL
with canonical quoting. CTAS also uses a different declaration printer. This
is a real compatibility gap. The earlier development run retained **16 such
differences in 20 cases**. A four-case ordinary-UPDATE diagnostic on the
published parent `ccde0f4` and candidate has identical outcomes: three reproduce
the rewrite and the 4096-byte localized rollback-mode case preserves the SQL.
This isolates an existing issue without pretending the parent supports jsonb;
it is not a replay of the full storage corpus and is excluded from fresh totals.

The storage inputs cross 11/12, 255/256 and 65535/65536-byte payload boundaries
and include nested large objects/arrays. Full output is compared in memory;
large observations are then stored as byte length and SHA-256, with a diagnostic
prefix in the final corpus. This report compression does not change acceptance.

The final full build passes **372 jobs**, all **316 executable tests**, **1,348
headline component proofs**, both audits and the reverse-file matrix. Four new
component theorems cover NULL, admitted BLOB identity, invalid text and empty
string classification; they do not prove all of SQLite's JSON behavior.
The nine native host bindings and native source remain unchanged. JSON text
subtypes, the other JSON functions, schema-text preservation, requested write
page geometry, cold-savepoint behavior and concurrent WAL locking remain open.

See `scripts/run-json-binary-*.py` and `docs/validation/sqlite-json-binary-*`.
Large reports are losslessly compressed; receipt hashes refer to their original
uncompressed bytes. The byte layout and semantics follow the pinned 3.53.4
`src/json.c`, with the [JSONB format](https://sqlite.org/jsonb.html) and
[function documentation](https://sqlite.org/json1.html#the_jsonb_function)
used as supplementary references.

## JSON pretty rendering with bounded traversal (2026-10-26)

`json_pretty()` now renders JSON/JSON5 text and admitted JSONB through pure
Lean. It handles default and custom indentation, SQL coercions and embedded-NUL
indent termination, escaped strings, JSON5 number normalization, nonminimal
binary headers, operation-local malformed-binary checks and depth diagnostics.
The renderer preserves raw result bytes. It collects output chunks and joins
them once, so a deep container does not repeatedly copy all descendant bytes.
The public function is available with one or two arguments, including the same
admission/error ordering used by the other implemented JSON functions.

Final frozen source: **ec3eabd77cd94afa61e550dbd9a103303fc5a6a5d29fe9dedb300ff7aac31b2c**.

| Final fresh JSON pretty corpus | Complete cases | Differences |
|---|---:|---:|
| read | 23648 | 0 |
| writer | 1840 | 0 |
| upstream | 16384 | 0 |
| Total | **41872** | **0** |

Read and writer seeds **355001 and 355002** use fresh values and unfiltered
mutations with maintained templates, across all eight page sizes and both
public file modes. Default and custom rendering run independently per input;
separate composition queries exercise JSONB input and error-position output.
Controls include indentation storage classes, invalid UTF-8, JSON5 escapes,
11/12, 255/256 and 65535/65536 payload boundaries, and depths 998 through 1001.
Full bytes, outcome and normalized first diagnostics must match. Read files
must remain unchanged. Writer checks include typed rows, schema shape, C
integrity, Lean reopen and a subsequent C write. Existing page-size conversion
is recorded separately.

Pinned SQLite `randomjson.c` supplies an independent corpus at fresh seeds
**3590000 through 3591023**: JSON/JSON5 text, binary versions and an unfiltered
mutation of every representation. Every input is separately executed with a
recorded indentation argument. The generator is loaded only by C; the public
Lean executable has no oracle dependency. Separate related JSONB regressions
pass **10736 cases** at seeds **355003 and 355004**.

The exact-schema large-storage corpus remains **64 differences in 80 cases**
at fresh seed **355005**. Full-image writes regenerate table SQL with canonical
quoting, and CTAS declaration spelling differs. These are the retained gaps
identified in the JSONB checkpoint; byte/row integrity observations still agree.
They are not counted as successes, and the overall final runner exits **1**.
No acceptance criterion was relaxed. Large read observations are compared in
full before being stored as SHA-256, length and a diagnostic prefix.

The first renderer and its chunk-based replacement each passed the same
**10,227 standalone interpreter controls**. These component/replay counts are
separate from fresh public coverage. **1,491 selected controls** remain in the
executable regression suite; input groups and fixed indices determined selection,
not passing outcomes. Initial prototype elaboration failed on a line continuation
before any runtime comparison; that draft and log remain available.

The first public candidate passed **268 writer cases**, but its read run was
intentionally interrupted after **920 seconds** because of repeated nested
copies. The read child exited **-2** and no complete read pass/failure count is
claimed. All checks after that interrupted job passed. After the chunk change,
the complete development replay passes **1,228 read cases** and **268 writer
cases**. Original source, interruption record and logs are retained.

A six-case fixed-depth diagnostic compares the same output before and after:
at depth 999, the length query took **15.29 -> 0.20 seconds**, and the complete
hex-output query **15.52 -> 0.53 seconds**, with identical outputs. These are
single diagnostic wall-time observations during development, not a statistical
benchmark or an overall database speed claim. The final fresh corpora run on
the optimized build.

The full build passes **374 jobs**, all **317 executable tests**, **1,352
headline component proofs**, both audits and the reverse-file matrix. Four new
component theorems cover NULL, empty quoting, empty hexadecimal payload rejection
and truncated binary headers; they do not prove total SQLite equivalence.
The native source and nine host bindings are unchanged. Other JSON functions,
JSON text subtype propagation, exact schema SQL, requested write page geometry,
cold-savepoint behavior and concurrent WAL locking remain open.

Harnesses are `scripts/run-json-pretty-*.py`; plans, negative records and logs
are retained under `docs/validation/sqlite-json-pretty-*`. Large reports are
losslessly compressed, with original and stored hashes. The pinned 3.53.4
`src/json.c` is the implementation reference; see also the
[SQLite JSON documentation](https://sqlite.org/json1.html#the_json_pretty_function).

## JSON binary extraction and deferred diagnostics (2026-10-26)

`jsonb_extract()` now traverses text/JSON5 and admitted JSONB through pure Lean.
One path returns SQL scalars or the original binary container slice; multiple
paths return a binary array. Numeric boundary conversion, noncanonical binary
payloads, exact string bytes, invalid UTF-8, NULL paths, missing paths and zero
or one argument follow pinned SQLite 3.53.4. The zero-argument star spelling is
normalized before evaluation. No C JSON implementation is used by the runtime.

Malformed descendants need two distinct behaviors. SQLite's internal text-to-blob
wrapper can return a partial binary even when its parser fails, so the Lean
translation retains that parser state. Rendering errors in multiple-path calls
are deferred: a later path error supersedes them, while NULL can discard a
pending malformed-JSON error. An already-reported nesting error survives NULL.
These are implemented as parser/error state, with no outcome filters or oracle
access. Assignment parsing now retries alternate row/group syntax only after a
syntax error, preserving resource-limit errors from a recognized scalar call.

Final frozen source: **8e1bab5fbd25bd98388571b4634cd58ff2e0e9ffd0019e75f87fcb89b5bf5ef7**.

| Final fresh JSON extraction corpus | Complete cases | Differences |
|---|---:|---:|
| read | 31232 | 0 |
| writer | 2272 | 0 |
| upstream | 32768 | 0 |
| Total | **66272** | **0** |

Read and writer seeds **355031 and 355032** use new values and unfiltered byte
mutations with maintained templates, all eight page sizes and both public file
modes. Root, selected-path and multi-path calls execute separately. This first corpus
compares quoted-value bytes; quote(TEXT) truncates at NUL. Exact SQL
storage classes, quoted-value bytes, normalized first errors and status must
match. Read files must remain byte-identical. Writers additionally check C
integrity, typed rows, schema shape, Lean reopen and subsequent C writes. Page
geometry is recorded separately from those result checks.

The independent pinned `randomjson.c` corpus uses fresh seeds **3610000 through
3611023**, all four JSON/JSON5 text/binary representations and an unfiltered
mutation of each. Root and recorded path-list requests run independently for
every input. Only the C oracle loads the generator. Related JSONB reads and
JSON-pretty writes pass **7584 cases** at seeds **355033 and 355034**.

An additional fresh final-checkpoint corpus compares `hex(value)` alongside
`hex(quote(value))`, so TEXT bytes after embedded NUL are observable. Its writer
also compares `hex(valid)` after persistence and includes NUL/invalid-UTF-8
strings. It passes **35552 cases** using read/write seeds **355046 and 355047**
and independent generator seeds **3620000 through 3620511**. These counts are
separate from the earlier quoted-output corpus. Both run the identical frozen
source and executable. A separate **11,443-case interpreter raw-byte replay**
also passes. Its first harness attempt duplicated imported declarations and did
not compile; that failure is retained and is not a semantic difference count.
The sixty expanded error controls were replaced with deterministic construction
before final evaluation; their exact ordered SQL lists were checked identical.

The separate exact-schema storage controls remain **64 differences in 80 cases**
at seed **355035**: full-image writes canonicalize table SQL and CTAS declaration
spelling. Byte/row integrity observations agree, but these catalog differences
remain failures and the combined final runner exits **1**. No acceptance rule
was weakened and no total SQL/database/WAL compatibility is claimed.

The standalone interpreter corpus contains **11,443 controls**. Its first test
formatter did not compile, so that attempt has no semantic evaluation result.
The corrected strict-parser prototype differed on **186 multiple-path cases**;
the partial-parser version passes all 11,443 on replay. These are component and
development results, separate from fresh public evaluation. **2,177 controls**
selected by input groups and fixed indices remain in the executable tests.

Initial public development recorded **4/3,536 read differences**, **4/264 writer
differences** and **1/2,048 upstream differences**. Deferred rendering diagnostics
and assignment-parser backtracking caused those failures. Their reports, source
and harness snapshots remain available. Sixty error-order controls and twenty
assignment-limit controls cover the fixes; the complete development replay
passes. Final testing uses the corrected frozen implementation and fresh seeds.

The full build passes **376 jobs**, all **319 executable tests**, **1,356 headline
component proofs**, both audits and the reverse-file matrix. Four new component
theorems cover no arguments, one argument, empty integer payloads and truncated
headers; they do not establish total SQLite equivalence. The native source and
nine host bindings are unchanged. JSON text subtype propagation, other SQL
features, exact schema SQL, write page geometry, cold savepoints and concurrent
WAL locking remain open.

Harnesses are `scripts/run-json-extract-*.py`; source, plans, negative records and
logs are under `docs/validation/sqlite-json-extract-*`. Large reports are losslessly
compressed with original/stored hashes. Pinned `src/json.c` is the implementation
reference; see the [SQLite extraction documentation](https://sqlite.org/json1.html#the_jsonb_extract_function).

## JSON SQL-value arrow, quoted calls and escape-tail consumption (2026-10-26)

The `->>` operator and its quoted function spelling now use pure JSONB lookup
and conversion. They accept full paths, abbreviated labels, integer indices
including negative indices, bracket paths and SQL-coerced path values. Scalars
retain SQL storage types; containers become compact JSON text. Raw TEXT bytes,
embedded NUL and invalid UTF-8 remain observable. Path errors retain the original
argument spelling. This function produces no JSON subtype.

Scalar preparation retains the operator's function flag for name resolution in
otherwise-dead AND branches. The SQL parser retains the original quoted function
token in excessive-argument diagnostics, separately from the decoded lookup name,
including brackets, backticks, escaped delimiters and assignment contexts.

Final frozen implementation: **5e31d65d7d46c7165b056c28dce87eda543289a9d0cd2cc1c89030da780f8b25**.

| Final fresh JSON arrow corpus | Complete cases | Differences |
|---|---:|---:|
| read | 39456 | 0 |
| writer | 2624 | 0 |
| upstream | 32768 | 0 |
| Total | **74848** | **0** |

Read/writer seeds **355101/355102** use fresh values and unfiltered mutations with
maintained templates, all eight page sizes and both public file modes. Root,
selected, quoted-function and chained requests run independently. Comparisons
include storage type, full `hex(value)` and `hex(quote(value))`, status and first
diagnostics. Fixed controls cover precedence, binding, dead branches, NULL,
numeric paths, escaped keys, nonminimal headers, malformed descendants, large
payloads and nesting boundaries. Read files must remain byte-for-byte unchanged.
Private read fixtures run in two workers; generation and collection retain their
original serial order. The original harness and scheduling transformation record
are preserved. No input generation or acceptance condition was relaxed.

Writer checks include C integrity, typed/raw persisted rows, schema shape, Lean
reopen and a subsequent independent C write. Requested page geometry is recorded
separately. Pinned `randomjson.c` supplies seeds **3670000–3671023**, four JSON/JSON5
text/binary representations and an unfiltered mutation of each. Only the C oracle
loads the generator. Related full-byte extraction regressions pass **18912**
cases at seeds **355103/355104**.

The first final candidate failed **2 of 39,456 arrow read cases**: a malformed
`\xE2` escape retained trailing bytes that C consumes. Its writer/upstream and
related extraction corpora passed, which did not establish decoder equivalence.
The shared decoder now consumes the remaining span when a putative line-separator
escape is invalid. Valid continuations and ordinary unknown escapes retain their
distinct behavior. The negative source, harnesses, reports and actual failed
process status are retained under `candidate1`.

A new public escape-tail corpus at seed **355105** passes **21984** cases across
both file modes and all page sizes. It covers raw and escaped text, continuations,
arbitrary suffix bytes, embedded NUL, nonminimal headers, and object-key matching
with different suffixes. Six operations run independently: arrow, binary extract,
type, array length, strict validity and error position. **606 fixed controls**,
including the discovered failure, are retained in executable tests. The development
replay and final fresh evaluations use the same frozen corrected implementation.

Earlier standalone quoted-output and raw-output component corpora each passed
**11,520 cases** using repeated inputs and separately seeded paths. They predate
the shared escape fix and are component/replay metrics, not final public coverage.
**2,254 selected component controls** remain in tests. Initial public development
had **4/4,416 read** and **24/324 writer** differences from lost quoted function
spelling; **2,048 upstream cases** passed. Those negative records remain, alongside
**45 direct spelling controls** and the subsequent passing development replay.

The full build passes **378 jobs**, **322 executable tests**, **1,361 headline
component proofs**, both audits and the reverse-file matrix. Four arrow theorems
cover NULL input, full-path identity, index zero and NULL path after successful
loading. A fifth theorem records malformed-separator span consumption. These are
component propositions, not a proof of total SQLite equivalence. Native code and
the nine host bindings remain unchanged.

The prior exact-schema checkpoint's **64/80 catalog SQL differences** remain open;
that separate corpus was not rerun here. Missing SQL features, JSON subtype
propagation, write geometry, cold savepoints and concurrent WAL locking also remain
open. No overall compatibility percentage is inferred. Reproducible plans,
source snapshots and negative records are under `docs/validation/sqlite-json-arrow-*`.
The pinned `src/json.c` is the implementation reference; see the
[SQLite arrow documentation](https://sqlite.org/json1.html#the_and_operators).

## Sequential binary JSON removal (2026-10-26)

`jsonb_remove()` now runs through the public pure Core SQL path. It accepts no
arguments, JSONB identity conversion without paths, and sequential removals.
Deleting an array element changes the indices observed by later paths. Deleting
an object field removes its label and value; repeated labels follow SQLite's
first-match behavior. Root and NULL paths preserve SQLite's short-circuit and
diagnostic ordering. The result is a BLOB without a JSON subtype.

The implementation uses the established lookup semantics, locates the selected
node's ancestors, removes the exact byte span, and updates affected payload-size
headers. Changed headers use minimum widths; untouched slices retain their bytes
and nonminimal headers. Malformed unused descendants are not eagerly validated.
Length adjustments follow the pinned implementation's unsigned 32-bit behavior.

Final frozen implementation: **7b069fa92feb76535400f87295d05fff0babbe3df6a76e54be2c94299191ce4f**.

| Final fresh binary-removal corpus | Complete cases | Differences |
|---|---:|---:|
| read | 31552 | 0 |
| writer | 2400 | 0 |
| upstream | 32768 | 0 |
| Total | **66720** | **0** |

Read/writer seeds **355081/355082** combine newly seeded values and unfiltered
mutations with maintained templates, all eight page sizes and both public file
modes. Identity, single-path and sequential-path requests run independently.
Comparisons include SQL storage type, full raw hex, quoted-value hex, status and
first diagnostics. Fixed cases include duplicated keys, NULL/error ordering,
malformed nodes, nonminimal headers, nesting limits and deletions crossing
ancestor-header size boundaries. Private read fixtures run in two workers with
serial generation and ordered collection. Files must remain unchanged by reads.

Writers compare outcomes, C integrity, typed/raw persisted values, schema shape,
Lean reopen and a subsequent independent C write. Page geometry is recorded
separately. The pinned upstream generator supplies seeds **3660000–3661023** in
four JSON/JSON5 text/binary representations, each with an unfiltered mutation.
Each input independently exercises identity and a sequential path list. Only the
C oracle loads this generator. Related arrow regressions pass **9840** cases
at seeds **355083/355084**. The development corpus passed **6,280 cases** before
the fresh final run; both runs use the same frozen implementation.

Standalone component evaluation passed **31,188 cases**, and a separately seeded
malformed-binary component corpus passed **16,384 cases**. Both corpora were
replayed after the shared escape-tail correction with identical inputs and
expected outputs and again passed. These are component/replay metrics, distinct
from public final coverage. **3,370 controls** selected by input groups and fixed
indices remain in the executable tests. Two failed proof-compilation drafts
(a nonexistent simplification lemma and an unreduced pure expression) are
retained; neither was a semantic evaluation result.

The full build passes **380 jobs**, **323 executable tests**, **1,365 headline
component proofs**, both audits and the reverse-file matrix. Four new theorems
cover no arguments, NULL input, admitted-BLOB identity and locating the current
node. They are component propositions, not a complete SQLite-equivalence proof.
Native code and the nine host bindings are unchanged.

The separate exact-schema checkpoint's **64/80 catalog SQL differences** remain
open and were not rerun here. Other SQL features, JSON subtype propagation, write
geometry, cold savepoints and concurrent WAL locking also remain open. No total
compatibility percentage is inferred. Harnesses and reproducible plans/source
records are under `scripts/run-json-remove-*` and `docs/validation/sqlite-json-remove-*`.
Implementation references are the pinned `src/json.c` and the
[SQLite removal documentation](https://sqlite.org/json1.html#the_jsonb_remove_function).

## Binary JSON merge patch (2026-10-26)

`jsonb_patch(target, patch)` now runs through pure Core SQL. Objects merge recursively,
NULL patch fields delete the first matching target field, and non-object patches
replace the target. Duplicate labels retain SQLite's scan and edit order. Target
loading precedes patch loading, including NULL and malformed-input behavior.

Edits preserve untouched byte slices. Short replacements reproduce SQLite's
header expansion when the same byte span can be reused. Recursive size changes
adjust only affected ancestors, including the pre-edit payload bounds used during
shrinking edits. The result is a BLOB without a JSON subtype.

Final frozen implementation: **90fed5428de4533ce806043c6a142a7598d63a9162ca20313eff326e5cf014f9**.

| Final fresh binary-patch corpus | Complete cases | Differences |
|---|---:|---:|
| read | 41152 | 0 |
| writer | 2464 | 0 |
| upstream | 32768 | 0 |
| Total | **76384** | **0** |

Read/writer seeds **355131/355132** combine fresh values and unfiltered mutations
with maintained templates, both public file modes and all eight page sizes.
Each input independently exercises an empty-object patch, two stored patches and
chained merging. Comparisons include storage type, full raw hex, quoted-value hex,
status and first diagnostics. Fixed controls cover argument admission, binding,
NULL/error ordering, duplicate labels, nested object deletion, malformed binary
members, nonminimal headers, nesting limits and header-width boundaries.

Writers compare C integrity, typed/raw persisted values, schema shape, Lean reopen
and a subsequent C write. Page geometry is recorded separately. The pinned
upstream generator supplies seeds **3690000–3691023**, four JSON/JSON5 text/binary
representations and an unfiltered mutation of each. Each input is tested with an
empty-object patch and a separately selected generated patch. Only the C oracle
loads the generator. Reads must preserve file bytes. Related removal regressions
pass **8464** cases at seeds **355133/355134**. The development corpus passed
**7,352 cases** before final evaluation, on the same frozen implementation.

Standalone component evaluation passed **12,215 cases** covering fixed documents,
malformed binary pairs, duplicate/escaped labels and overwrite-header expansion.
A separate component corpus passed **6,164 cases**, including seeded structured
binary pairs, seeded text objects and fixed nesting boundaries. These are
component metrics, not public file coverage. **2,925 controls**, selected by input
groups and fixed indices without outcome filtering, remain in executable tests.

The full build passes **382 jobs**, **324 executable tests**, **1,369 headline
component proofs**, both audits and the reverse-file matrix. New component
theorems cover NULL target, NULL patch after target loading, zero header
expansion and reaching the end of member search. They do not establish total
SQLite equivalence. Native code and the nine host bindings are unchanged.

The separate exact-schema checkpoint's **64/80 catalog SQL differences** remain
open and were not rerun here. Missing SQL features, JSON subtype propagation,
write geometry, cold savepoints and concurrent WAL locking also remain open.
No total compatibility percentage is inferred. Reproducible harnesses, plans and
source records are under `scripts/run-json-patch-*` and
`docs/validation/sqlite-json-patch-*`. Implementation references are the pinned
`src/json.c` and the
[SQLite merge-patch documentation](https://sqlite.org/json1.html#the_jsonb_patch_function).

## Text JSON and runtime subtype boundaries (2026-10-26)

The public Core path now evaluates `json`, `json_extract`, `json_remove`,
`json_patch`, the `->` operator and `subtype`. JSON text results carry subtype
74 as runtime value metadata. Single-path extraction of a scalar returns the
ordinary SQL value without that tag; missing and NULL results retain subtype
zero. Parsing, lookup, rendering and mutation use the existing pure Lean JSON
components. The pinned SQLite 3.53.4 executable is an external comparison
oracle only. The [upstream JSON documentation](https://sqlite.org/json1.html)
and the pinned `src/json.c` informed the behavior; executable observations fix
the version-specific details.

Subtype metadata travels through selected CASE/iif/coalesce/nullif and scalar
MIN/MAX operands, unary plus, COLLATE and CAST AS TEXT. Ordinary computations
and CAST AS BLOB clear it. Aggregate MIN/MAX retain the selected input's actual
metadata through result slots, grouped/joined projections and HAVING. Runtime
write candidates retain it through affinity, DEFAULT substitution and RETURNING.
Constraint replacement uses one shared generic loop, so a needed DEFAULT is
evaluated once. Physical Core values and database records contain no subtype.

For example, a single-row `INSERT ... VALUES(json('{}')) RETURNING subtype(v)`
returns 74; a later stored read returns zero. Multi-VALUES and INSERT SELECT
materialize their source values and clear their tags, while defaults evaluated
for the destination still carry their own tags. Rowid allocation/conversion
clears the rowid tag. OR ABORT RETURNING now also reports the ordered NOT NULL
constraint diagnostic instead of the internal generic row-validation error.

The final frozen checkpoint `67dae00baeab27033110d72ede9be7f70ca970c14f8dbe785de73d19d99b73fb` completed these public comparisons.
Read, generator and related-function receipts come from the first final
candidate; the writer and final checks come from the second run. The source
and executable are identical across both runs:

| Suite | Requests | Differences |
| --- | ---: | ---: |
| read | 76112 | 0 |
| upstream | 65536 | 0 |
| writer | 5152 | 0 |

These 146800 requests combine fixed templates with newly seeded data. Read
seed 355161 and write seed 355202 exercise both public file engines across
512–65536-byte source pages. They compare type, subtype, complete raw result
bytes, quoted bytes, status and the first diagnostic. Binary header boundaries,
invalid UTF-8, embedded NULs, malformed inputs and nesting limits remain in the
corpus. Read fixtures must remain byte-identical and pass C integrity checks.
Writes compare persisted rows, schema shape, reopen results and a subsequent
independent C write; page geometry is recorded separately. The upstream random
JSON generator uses fresh seeds 3710000–3710511, including unfiltered mutations.
A further 10608 fresh related binary-merge-patch requests passed with seeds
355163–355164. These measurements are scoped differential evidence, not a
percentage of all SQLite behavior or a proof of complete file/WAL compatibility.

Development replay separately passed 9620 reads, 840 writes and 8192 upstream
requests. Earlier standalone component checks passed 21026 direct JSON cases
and 4999 nested scalar cases. A Core runtime component passed 1452 cases after
its diagnostic correction. Tests retain 1928 direct, 1144 scalar and all 1452
runtime controls. The component corpora and replays are not fresh final public
coverage. The full 386-job build, all 327 executable test groups, the native/
proof audit, all 1383 registered headline declarations, the live-path checks
and the full reverse comparison passed. The declaration count refers to
component contracts, not a whole-SQLite equivalence theorem. The existing nine
native bindings and native source hash are unchanged.

Negative results are preserved. The first public development run found 60
aggregate-tag and 20 UPDATE RETURNING-tag differences; it also exposed stale
live-path patterns. The expanded runtime component found 24 OR ABORT NOT NULL
diagnostic differences before their correction. The second writer attempt
completed its loops but failed its own final hash guard because a loop variable
shadowed the recorded source hash; it produced no accepted writer metric. The
outer runner independently confirmed that source and executable were unchanged.
Subsequent live-path attempts found remaining pre-typed DEFAULT, AUTOINCREMENT
and BETWEEN patterns, all updated to check the actual runtime calls. Failed
prototype/harness compilations and two full-build proof failures are retained
with their sources, logs and actual exit statuses. No failed cases were removed
to obtain a passing comparison.

The first final writer measured 5152 requests with 80 differences. All 80
had identical error messages and persisted/reopened/follow-up observations;
C printed a following SELECT because its CLI continues same-line statements
even with `-bail`. A separate four-observation control reproduces this with
ordinary integer overflow, without JSON. All five distinct failing templates
match when statements are delivered on separate input lines. The revised
writer uniformly applies that delivery to every case, preserves each original
template, and compares full output without filtering. Seven quote/comment
controls check that semicolons inside SQL tokens are not split. Fresh seed
355202 provides the reported final writer evidence. The original 80 CLI
continuation differences remain recorded; SQL statement delivery does not
implement or claim full SQLite CLI compatibility. No production change was
made in response to this delivery discrepancy.

This checkpoint does not finish SQLite compatibility. JSON constructors,
editing functions and JSON aggregates still need implementation and independent
public evaluation, along with the previously recorded SQL, schema, catalog SQL,
write-geometry, cold-savepoint and concurrent-WAL gaps. See the checkpoint
receipt and the losslessly compressed reports under `docs/validation/`; the
artifact manifest records the stored hashes and the compression manifest also
records original report hashes.

## JSON constructors and quoted values (2026-10-26)

The public Core path now evaluates `json_quote`, `json_array`, `jsonb_array`,
`json_object` and `jsonb_object`. The implementation uses pure Lean JSON
rendering, quoting and JSONB encoding. It consumes each argument's actual
runtime subtype: ordinary TEXT is quoted, subtype-74 TEXT is appended as JSON,
and accepted JSONB BLOBs are rendered. Object labels must be TEXT, duplicate
labels remain in order, and all five scalar constructors return subtype 74.
The pinned SQLite 3.53.4 executable remains an external comparison oracle.
The [JSON function documentation](https://sqlite.org/json1.html) and pinned
`src/json.c` provide the source reference; executable observations determine
version-specific behavior on malformed input.

Construction retains SQLite's deferred buffer-error behavior. A later malformed
primitive JSONB value can replace an earlier invalid-BLOB diagnostic, while a
later non-TEXT object label overrides pending value errors. Binary construction
also preserves the pinned implementation's partial parser output for malformed
subtype-tagged TEXT. These behaviors are measured without filtering malformed
inputs or normalizing successful output.

The final frozen checkpoint `46ca0651fde67a36e16548f6523cdcccf5d84a21d5b96c7a71761180af531493` completed these public comparisons:

| Suite | Requests | Differences |
| --- | ---: | ---: |
| read | 72928 | 0 |
| writer | 5152 | 0 |
| upstream | 65536 | 0 |

These 143616 requests combine fixed templates with newly seeded data. Read
seed 355231 and write seed 355232 cover both public file modes across 512–65536
byte source pages. Comparisons include SQL type, subtype, full raw result bytes,
quoted bytes, success/error status and the first diagnostic. Controls retain
embedded NULs, invalid UTF-8, all JSONB root kinds, header boundaries, nesting
limits, argument-count errors, dead branches, nested constructors, aggregates
and RETURNING. Read files must remain byte-identical and pass independent C
integrity checks. Writes compare stored bytes, schema shape, reopen results and
a subsequent C write; page geometry is recorded separately. The upstream JSON
and JSON5 generator uses fresh seeds 3740000–3740511, with unfiltered mutations.
A further 10460 fresh requests check the existing text JSON implementation
with seeds 355233–355234. This evidence is scoped to these suites; it is not a
percentage of all SQLite behavior or complete database/WAL compatibility.

Development public checks separately passed 8824 reads, 840 writes and 8192
upstream requests. Their seven individual job receipts all record exit zero;
the development runner's last tool output was truncated, so no outer runner
exit is inferred. The final runner's exit is captured directly by its subprocess
wrapper. Earlier component checks passed 8905 direct-constructor cases and
13112 nested-expression cases. Those are component measurements, not public
admission or file coverage. Tests retain 2689 fixed-index and regression controls.
The 388-job full build, 328 executable test groups, native/proof audit, 1390
registered headline declarations, live-path checks and full reverse comparison
passed. The declarations are component contracts, not a whole-SQLite equivalence
theorem. The existing nine native bindings and native source hash are unchanged.

Negative results remain available. The initial 8905-case component run found
92 diagnostic differences caused by later primitive JSONB nodes being visited
after an earlier buffer error. The correction retains every case, and all 92
are included in the maintained regression controls. The failed proof prototype
and its corrected source are also preserved. The writer uniformly delivers
statements on separate input lines, retaining original templates, as documented
in the preceding text JSON checkpoint. It does not filter output or implement
the remaining same-line SQLite CLI continuation policy.

JSON editing functions and JSON aggregates still need implementation and
independent public evaluation. The previously recorded SQL, schema/catalog SQL,
write-geometry, cold-savepoint and concurrent-WAL gaps also remain open. Reports,
source patches, logs and receipts are under `docs/validation/`; large reports
are losslessly compressed, with both original and stored hashes recorded.

## Ordinary JSON aggregates and INSERT preparation (2026-10-26)

The public Core path now evaluates `json_group_array`, `jsonb_group_array`,
`json_group_object` and `jsonb_group_object`. Actual argument values and subtype
metadata pass through the existing shared accumulator, DISTINCT handling,
FILTER, aggregate ORDER BY, grouped/joined execution, HAVING and scalar result
expressions. Object values retain their own metadata in the sorter's second
argument. SQL execution and JSON encoding remain pure Lean; the pinned SQLite
3.53.4 executable is an external comparison oracle only. The
[JSON function documentation](https://sqlite.org/json1.html) and pinned
`src/json.c` provide the source reference, with observed behavior fixed to the
pinned version.

Object aggregate keys are coerced to TEXT and truncated at the first NUL.
NULL keys suppress their entries, while their argument expressions are still
evaluated. Duplicate keys remain in order. The implementation also retains the
upstream null-entry marker cleanup, including its interaction with malformed
subtype-tagged TEXT. Invalid non-JSONB BLOBs and excessive JSON nesting abort a
step immediately; malformed JSONB buffer errors remain deferred until the
aggregate finishes. These distinct error timings matter when another row or
aggregate would also fail.

Text results and binary object results carry subtype 74. In this SQLite
version, a nonempty `jsonb_group_array` returns subtype zero, while an empty
one returns subtype 74; this distinction is preserved explicitly. Physical
storage still carries no runtime subtype. Ordinary aggregation is covered here;
window execution is not implemented by this checkpoint.

RETURNING now reports the offending aggregate function name and its arity
errors. VALUES preparation checks row-width consistency, target names, source
name/function binding and target arity before RETURNING binding, including the
AUTOINCREMENT path. This preparation never evaluates runtime expressions.
`DEFAULT VALUES` retains its separate empty-source behavior. The change does
not claim complete INSERT SELECT preparation or support for new subqueries.

The final frozen checkpoint `925cc245d3eaedc7ffcf9a8ee1b83c15bd7be6c5545aefa7f6be5c686c044af9` completed these public comparisons:

| Suite | Requests | Differences |
| --- | ---: | ---: |
| read | 73856 | 0 |
| writer | 13248 | 0 |
| upstream | 65536 | 0 |

These 152640 requests combine fixed templates with newly seeded data. Read
seed 355261 and write seed 355262 exercise both public file engines across
512–65536-byte source pages. They compare SQL type, subtype, full raw result
bytes, quoted bytes, status and the first diagnostic. They include malformed
UTF-8, NULs, JSONB root kinds, nesting and header boundaries, empty groups,
NULL/duplicate keys, ordering, filtering, DISTINCT, unmatched joined rows,
interleaved aggregate/row errors and persisted output. Read files must remain
byte-identical and pass independent C integrity checks. Writes compare stored
bytes, schema shape, reopen results and a subsequent C write; write geometry
is recorded separately. The upstream JSON/JSON5 generator uses new seeds
3760000–3760511, retaining unfiltered mutations. Another 12648 fresh requests
check existing constructors and percentile/numeric aggregation with seeds
355263–355266. These are scoped comparisons, not a global SQLite compatibility
percentage or proof of complete database/WAL equivalence.

Development evidence is reported separately: the first candidate passed 12864
reads and 8192 upstream requests; the corrected final-source writer replay
passed 3088 requests. Earlier state components passed 8338 ordinary cases and
1312 header/depth/error-timing cases. The first component was replayed after
the depth correction. These component and development runs are not fresh final
public coverage. Tests retain 1929 fixed-index state controls, 240 RETURNING
diagnostic controls and 64 INSERT preparation controls, 2233 in total. The
392-job full build, 329 executable test groups, native/proof audit, 1402
registered headline declarations, live-path checks and full reverse comparison
passed. The declarations describe component contracts rather than whole-SQLite
equivalence. The existing nine native bindings and native source hash are
unchanged.

Negative results are preserved. The first boundary component found 24 errors
in when excessive nesting aborted a step. The corrected implementation passes
all 1312 original cases without exclusions. Two early proof attempts failed
because scalar values lacked decidable equality and because encoded parser
output did not reduce to a literal array; the maintained proofs directly state
empty-result delegation and runtime subtype contracts, while executable tests
check encoded bytes. The first full build failed on two record-expression
continuation lines; its source and log remain available.

The first public writer found 16 differences in RETURNING aggregate diagnostic
names. After their correction, an expanded writer found 192 INSERT preparation
differences: the shared three-value RETURNING controls met the file fixture's
four-column table, exposing target-arity errors that C reports before RETURNING.
The original inputs were retained. The preparation correction fixes those
cases and is checked by 64 additional target/source/arity controls. The final
development writer replay passes all 3088 requests. Earlier reports, sources,
script snapshots and process exits are retained; no failing queries were
removed to produce a passing count.

JSON editing functions and the previously recorded SQL, schema/catalog SQL,
write-geometry, cold-savepoint and concurrent-WAL gaps remain open. The writer
uses the documented statement-per-line CLI delivery and retains original SQL
templates; it does not implement full SQLite CLI continuation behavior. Reports,
source patches, logs and receipts are under `docs/validation/`, with original
and stored hashes for losslessly compressed reports.
