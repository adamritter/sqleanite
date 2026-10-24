# SQLite C-to-Lean port: scalar values, text/blob functions and column affinity

This is an incremental port, **not a complete SQLite implementation**. The
reference is SQLite **3.53.4**, checkout `b09c88c14082339b66c7b7158d609a771e64ca69`
in the adjacent `sqlite/` directory. All implementation changes in this step
are Lean. The existing OS bindings are unchanged; the engine does not call C
SQLite. C SQLite is used only as an independent test oracle.

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

Validated on Lean 4.35.0: all 160 executable tests, all 924 registered headline
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
values, constant UPDATE assignments and supported predicate operands. They do
not yet make row-dependent projection or UPDATE expressions available.

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

## Still missing

This step does not implement row-dependent projection/UPDATE expressions,
the complete VDBE, the full planner, all DDL/constraints, views/triggers,
subqueries/CTEs/windows, the rest of the scalar/aggregate functions, JSON,
virtual tables/extensions, all collations/encodings, or the full SQLite WAL
and locking protocol. Tableless ORDER BY and aggregates are still rejected.
This is the default 17-digit REAL formatting path, not general SQLite printf
or per-connection floating-point precision configuration.

Stored column affinity is implemented for the admitted Core SQL subset.
Comparisons that would require converting the stored column to a different
affinity (for example TEXT-column versus CAST-to-INTEGER, or TEXT/NUMERIC joins)
are explicitly rejected pending a general row-expression evaluator. Admitted
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
