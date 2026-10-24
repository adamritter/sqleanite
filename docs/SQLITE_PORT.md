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

## Still missing

This step does not implement general aggregate/join/write WHERE or row-dependent UPDATE expressions,
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
