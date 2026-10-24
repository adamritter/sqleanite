#!/usr/bin/env python3
"""Compare the production Lean file engine with the C SQLite CLI.

SQLite creates the oracle file. Python's SQLite binding only observes both
files, including storage classes, exact binary64 bits and TEXT/BLOB bytes.
It is not used by the Lean engine. Seeded cases are reproducible.
"""
import argparse
import json
import pathlib
import random
import sqlite3
import struct
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]


def corpus():
    cases = []

    def add(group, *expressions):
        cases.extend((group, expression) for expression in expressions)

    add("arithmetic", "-1.5", "-0.0", "-(0.0)", "-'0.0'", "-CAST(0 AS REAL)",
        "-(-0.0)", "-(0.0+0.0)", "+'12'", "-'12'", "-NULL", "-(-9223372036854775808)",
        "9223372036854775807+1", "-9223372036854775808-1",
        "3037000500*3037000500", "-9223372036854775808/-1",
        "-9223372036854775808%-1", "-7/3", "7/-3", "-7%3", "7%-3",
        "1/0", "1.0/0", "5%0.1", "1e999-1e999", "0*1e999", "1e999/1e999",
        "5.5%2", "5%'2.0'", "5%'2e1'", "5%'abc'", "NULL+1", "1+NULL")
    texts = ["", " ", "abc", "12xyz", "  -12tail", "1.5x", "1e2x", "1e+", ".5",
             "1.", "0x10", "9223372036854775808", "-9223372036854775809",
             "1e999", "-1e999", "1e-999", "1.0", "2.0", "2251799813685248.0",
             "2251799813685247.0", "-2251799813685248.0", "123e+5", "\t\n42\r"]
    for source in texts:
        literal = "'" + source + "'"
        add("numeric-prefix", literal + "+0", "NOT " + literal)
        for target in ["INTEGER", "REAL", "NUMERIC"]:
            add("cast", f"CAST({literal} AS {target})")
    for source in ["X'31322E3578'", "X'3132FF'", "X'003132'", "X'31320078'", "X''"]:
        add("blob-numeric", source + "+0", f"CAST({source} AS INTEGER)",
            f"CAST({source} AS REAL)", f"CAST({source} AS NUMERIC)")
    for value in ["0", "1", "-1", "-9223372036854775808", "9223372036854775807"]:
        add("bitwise", "~(" + value + ")")
        for amount in [-9223372036854775808, -65, -64, -63, -1, 0, 1, 63, 64, 65]:
            add("bitwise", f"({value})<<({amount})", f"({value})>>({amount})")
    for a in ["NULL", "0", "1", "'0.5x'", "'abc'"]:
        for b in ["NULL", "0", "1"]:
            add("boolean", f"({a}) AND ({b})", f"({a}) OR ({b})")
    for a, b in [("NULL", "NULL"), ("1", "1.0"), ("'1'", "1"),
                 ("9223372036854775807", "9223372036854775808"),
                 ("X'41'", "'A'"), ("'árvíz'", "'árok'")]:
        for op in ["=", "!=", "<", "<=", ">", ">=", "IS", "IS NOT"]:
            add("comparison", f"({a}) {op} ({b})")
    for a, b in [("CAST(1 AS INTEGER)", "'1'"), ("CAST(1 AS TEXT)", "1"),
                 ("CAST(1 AS INTEGER)", "'1x'"), ("CAST(1 AS INTEGER)", "X'31'"),
                 ("+CAST(1 AS INTEGER)", "'1'"), ("CAST(1 AS INTEGER)", "CAST('1' AS TEXT)")]:
        for op in ["=", "<", "IS", "IS NOT"]:
            add("cast-comparison-affinity", f"({a}) {op} ({b})")
    add("case-affinity", "CASE CAST(1 AS INTEGER) WHEN '1' THEN 1 ELSE 0 END",
        "CASE '1' WHEN CAST(1 AS INTEGER) THEN 1 ELSE 0 END")
    add("static-boolean", "0 AND abs(-9223372036854775808)",
        "1 OR abs(-9223372036854775808)", "FALSE AND abs(-9223372036854775808)",
        "abs(-9223372036854775808) OR (0 OR 2)")
    add("lazy", "coalesce(NULL, 7, abs(-9223372036854775808))",
        "ifnull(8, abs(-9223372036854775808))",
        "iif(0, abs(-9223372036854775808), 9)", "iif(0, 1)",
        "iif(0, 1, NULL, 2, 1, 3, abs(-9223372036854775808))",
        "CASE WHEN NULL THEN 1 WHEN '0.5' THEN 2 ELSE 3 END",
        "CASE 1 WHEN 1.0 THEN 7 ELSE abs(-9223372036854775808) END",
        "CASE NULL WHEN NULL THEN 1 ELSE 2 END", "CASE WHEN 0 THEN 1 END")
    add("collation-metadata", "coalesce(1,2 COLLATE NOCASE)")
    add("builtins", "typeof(1+1)", "typeof(1.0+1)", "abs(-12)", "abs('-12')",
        "abs('abc')", "abs(NULL)", "length('árvíz')", "octet_length('árvíz')",
        "length(X'00FF41')", "length(CAST(X'410042' AS TEXT))",
        "octet_length(CAST(X'410042' AS TEXT))", "upper('Árvíz abc')", "lower('ÁRVÍZ ABC')",
        "nullif(1,1.0)", "nullif(1,'1')", "typeof(NULL)", "NULL IS NULL",
        "1 IS NOT NULL", "'ab'||42", "X'41'||'B'", "NULL||'x'",
        "CAST(123 AS TEXT)", "CAST('árvíz' AS BLOB)", "CAST(1.5 AS NUMERIC)",
        "CAST('12.5' AS FLOAT)", "CAST('12.5' AS STRING)")
    add("embedded-nul", "CAST(X'31320078' AS TEXT)+0",
        "CAST(CAST(X'31320078' AS TEXT) AS NUMERIC)",
        "CAST(12 AS INT)=CAST(X'31320078' AS TEXT)",
        "CAST(X'3932323333373230333638353437373538303700' AS NUMERIC)")
    rng = random.Random(3534)
    for _ in range(250):
        a = rng.randint(-(1 << 63), (1 << 63) - 1)
        b = rng.choice([0, -1, 1, rng.randint(-(1 << 63), (1 << 63) - 1)])
        op = rng.choice(["+", "-", "*", "/", "%", "&", "|", "<<", ">>"])
        add("seeded-integer", f"({a}){op}({b})")
    rng = random.Random(122)
    for _ in range(200):
        source = f"{rng.randrange(-10**17, 10**17)}e{rng.randrange(-300, 301)}"
        add("seeded-real", f"CAST('{source}' AS REAL)",
            f"CAST(CAST('{source}' AS REAL) AS TEXT)")
    for source in ["49.47", "0.1", "0.0", "-0.0", "1e16", "1e17", "1e-4", "1e-5",
                   "1.7976931348623157e308", "2.2250738585072014e-308",
                   "4.9406564584124654e-324", "2.4703282292062327e-324",
                   "2.4703282292062328e-324", "1e999", "-1e999", "0e999",
                   "123456789012345678901234567890.123456789"]:
        add("real-boundary", f"CAST('{source}' AS REAL)",
            f"CAST(CAST('{source}' AS REAL) AS TEXT)", f"length(CAST('{source}' AS REAL))")
    return cases


def observe(path):
    with sqlite3.connect(path) as db:
        db.text_factory = bytes
        assert db.execute("PRAGMA integrity_check").fetchone() == (b"ok",)
        rows = []
        for key, kind, value in db.execute("SELECT id,typeof(v),v FROM t ORDER BY id"):
            if isinstance(value, float):
                value = struct.pack(">d", value).hex()
            elif isinstance(value, bytes):
                value = value.hex()
            rows.append((key, kind.decode(), value))
        return rows


def run(args, cwd, source):
    query = cwd / "query.sql"
    query.write_text(source)
    result = subprocess.run([str(args.lean), "--verified-file", str(cwd / "lean.db"), str(query)],
                            capture_output=True, text=True, timeout=120)
    reference = subprocess.run([args.sqlite, "-batch", "-bail", str(cwd / "sqlite.db")],
                               input=source, capture_output=True, text=True, timeout=120)
    return result, reference


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=pathlib.Path, default=ROOT / ".lake/build/bin/sqleanite")
    parser.add_argument("--sqlite", default="/usr/bin/sqlite3")
    parser.add_argument("--output", type=pathlib.Path)
    args = parser.parse_args()
    cases = corpus()
    with tempfile.TemporaryDirectory(prefix="sqleanite-scalar-") as tmp:
        cwd = pathlib.Path(tmp)
        source = "CREATE TABLE t(id INTEGER PRIMARY KEY,v);\nBEGIN;\n" + "\n".join(
            f"INSERT INTO t VALUES({i}, {expr});" for i, (_, expr) in enumerate(cases, 1)) + "\nCOMMIT;"
        actual, expected = run(args, cwd, source)
        if actual.returncode or expected.returncode:
            raise RuntimeError(f"Lean: {actual.stdout}{actual.stderr}\nSQLite: {expected.stdout}{expected.stderr}")
        lean_rows, sqlite_rows = observe(cwd / "lean.db"), observe(cwd / "sqlite.db")
        assert len(lean_rows) == len(sqlite_rows) == len(cases)
        failures = [dict(id=i, group=cases[i-1][0], expression=cases[i-1][1],
                         lean=a, sqlite=b) for i, (a, b) in enumerate(zip(lean_rows, sqlite_rows), 1) if a != b]
        # Exercise persisted UPDATE, indexed predicate operands and reopen.
        source = "UPDATE t SET v=6*7 WHERE id=1+1; SELECT id,v FROM t WHERE id=CAST('2x' AS INTEGER);"
        actual, expected = run(args, cwd, source)
        assert actual.returncode == expected.returncode == 0, (actual.stderr, expected.stderr)
        assert actual.stdout == expected.stdout == "2|42\n", (actual.stdout, expected.stdout)
        queries = ["SELECT 6*7;", "SELECT CAST('12x' AS INTEGER), typeof(1.0+1);",
                   "SELECT abs(-9223372036854775808) WHERE 0;",
                   "SELECT abs(-9223372036854775808) LIMIT 0;",
                   "SELECT abs(-9223372036854775808) LIMIT 1 OFFSET 1;",
                   "SELECT 1 WHERE '0.5x';", "SELECT 1 UNION ALL SELECT 2;",
                   "SELECT CASE 1 WHEN 1.0 THEN 7 ELSE abs(-9223372036854775808) END;"]
        for query in queries:
            actual, expected = run(args, cwd, query)
            assert actual.returncode == expected.returncode == 0, (query, actual.stderr, expected.stderr)
            assert actual.stdout == expected.stdout, (query, actual.stdout, expected.stdout)
        before = observe(cwd / "lean.db")
        errors = ["+0 AND abs(-9223372036854775808)",
                  "2147483648 OR abs(-9223372036854775808)", "abs(-9223372036854775808)", "abs()", "coalesce(1)",
                  "CASE WHEN 1 THEN abs(-9223372036854775808) ELSE 0 END"]
        for expression in errors:
            actual, expected = run(args, cwd, f"INSERT INTO t VALUES(99999,{expression});")
            assert actual.returncode != 0 and expected.returncode != 0, expression
            assert observe(cwd / "lean.db") == before, expression
        # Unsupported syntax must be rejected even in unevaluated branches.
        for expression in ["coalesce(1,missing_column)", "coalesce(1,unknown_function())"]:
            actual, _ = run(args, cwd, f"INSERT INTO t VALUES(99999,{expression});")
            assert actual.returncode != 0, expression
            assert observe(cwd / "lean.db") == before, expression
        report = {"cases": len(cases), "failures": failures, "errors": len(errors),
                  "sqlite_version": subprocess.check_output([args.sqlite, "--version"], text=True).strip(),
                  "comparison": "storage class, exact binary64 bits, raw text/blob bytes; integrity_check"}
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))
        return bool(failures)


if __name__ == "__main__":
    raise SystemExit(main())
