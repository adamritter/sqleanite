# SQLite C-to-Lean port: scalar value layer

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
| `build.c`: `sqlite3AffinityType` | `SQLite/Scalar.affinity` | Type-name precedence for CAST; this does **not** yet add stored column affinity |
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

Validated on Lean 4.35.0: all 157 executable tests, all 914 registered headline
theorems, the verification audit and the live-path audit pass. The new suite
matches **1,114 expressions** exactly and checks six expected evaluation/arity
errors. The 13 existing Core differential cases and 20 reverse-compatibility
cells pass; three reverse cells remain deliberately rejected. The 11 forward
workloads retain their existing result: ten fully clean, and the indexed-shrink
case with its previously declared two allocated-but-unreferenced pages.

The separate 144-probe SQL-surface audit improves from 44 to 46 matching probes,
with no additional mismatches. It still reports the same three semantic gaps
listed below. Of its 106 equally weighted feature groups, 25 match all sampled
cases, 12 are partial, 66 are rejected and three differ. These samples are not
coverage of the whole SQLite codebase. Local raw logs and reports are in
`../benchmarks/20261024-sqlite-scalar-port/` (outside this Git repository).

## Still missing

This step does not implement row-dependent projection/UPDATE expressions,
the complete VDBE, the full planner, all DDL/constraints, views/triggers,
subqueries/CTEs/windows, the rest of the scalar/aggregate functions, JSON,
virtual tables/extensions, all collations/encodings, or the full SQLite WAL
and locking protocol. Tableless ORDER BY and aggregates are still rejected.
This is the default 17-digit REAL formatting path, not general SQLite printf
or per-connection floating-point precision configuration.

The earlier audit's column-affinity, column-collation and WITHOUT ROWID
compatibility gaps are **not fixed** here. CAST affinity in constant expressions
must not be confused with column affinity in stored schemas and predicates.
Invalid UTF-8 BLOB-to-TEXT conversion is explicitly rejected rather than
replacing bytes. Collations and column references in constant expressions are
rejected, including in dead branches. Do not infer a percentage of SQLite
coverage from the number of ported functions or passing test expressions.
