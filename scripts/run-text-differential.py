#!/usr/bin/env python3
"""Exact production-file differential tests for SQLite string/blob scalars.

C SQLite is an independent oracle only. The Lean executable writes its own file;
Python only observes the files' types, binary64 bits, bytes and integrity.
A different --seed gives fresh final-checkpoint cases without changing the suite.
"""
import argparse
import importlib.util
import hashlib
import json
import pathlib
import random
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("scalar_differential", ROOT / "scripts/run-scalar-differential.py")
scalar = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scalar)


def text_literal(value):
    return "CAST(X'" + value.encode("utf-8").hex() + "' AS TEXT)"


def blob_literal(value):
    return "X'" + value.hex() + "'"


def corpus(seed, count):
    cases = []

    def add(group, *exprs):
        cases.extend((group, expr) for expr in exprs)

    add("raw-text", "char(55296)", "trim(X'FF')")
    values = ["NULL", "0", "-12", "1.5", "''", "'árvíz🙂'", "X''", "X'00FF80'",
              text_literal("a\x00b"), text_literal(" \txy \x00 ")]
    for value in values:
        add("bytes", f"hex({value})", f"quote({value})", f"sign({value})")
    for value in values:
        for start in [-9223372036854775808, -20, -3, -1, 0, 1, 2, 4, 20, 9223372036854775807]:
            add("substring", f"substr({value},{start})")
            for length in [-9223372036854775808, -20, -2, -1, 0, 1, 2, 20, 9223372036854775807]:
                add("substring", f"substr({value},{start},{length})")
    add("substring", "substring('abcdef',3,-2)", "substr('abc',NULL)",
        "substr('abc',1,NULL)", "substr('abc','2x','2.8')")
    for a, b in [("'árvíz'", "'ví'"), ("'abc'", "''"), ("''", "''"),
                 ("X'00FF0041'", "X'0041'"), ("X'6162'", "'b'"),
                 (text_literal("a\x00β"), text_literal("\x00β")),
                 ("NULL", "'x'"), ("'abc'", "'x'"), ("12345", "34")]:
        add("instr", f"instr({a},{b})")
    for name in ["trim", "ltrim", "rtrim"]:
        for source in ["'  hello  '", "'xyabxy'", "'🙂árvíz🙂'", text_literal(" a\x00 "), "NULL", "42"]:
            add("trim", f"{name}({source})")
            for chars in ["''", "'xy'", "'🙂'", "NULL", text_literal(" \x00x")]:
                add("trim", f"{name}({source},{chars})")
    for value in ["''", "'00ff41'", "'123'", "'AB CD'", "'A BCD'", "' AB CD '",
                  "'4a🙂ff'", "'x'", "NULL", "1234", text_literal("41\x00zz")]:
        add("unhex", f"unhex({value})")
        for ignore in ["' '", "'🙂'", "'x'", "'ABC'", "NULL"]:
            add("unhex", f"unhex({value},{ignore})")
    add("replace", "replace('ababa','aba','X')", "replace('abc','','x')",
        "replace('abc','',NULL)", "replace('abc','b',NULL)", "replace(NULL,'','x')",
        f"replace({text_literal('a' + chr(0) + 'ba')},'a','Z')",
        f"replace({text_literal('a' + chr(0) + 'b')},{text_literal(chr(0))},'x')",
        f"replace({text_literal('a' + chr(0) + 'ba')},{text_literal('a' + chr(0))},'X')")
    add("concat", "concat(NULL)", "concat(NULL,NULL)", "concat('',NULL,'',1.0)",
        "concat_ws('-',NULL,'',NULL,'')", "concat_ws(NULL,'a','b')", "concat_ws('-',NULL,NULL)",
        f"concat({text_literal('a' + chr(0))},'β',X'63')",
        f"concat_ws({text_literal(chr(0))},'a','','b')")
    add("unicode", "char()", "char(NULL,65,128578)", "char(-1,1114112,9223372036854775807)",
        "char(0,65,1114111)", "unicode('')", "unicode(NULL)", "unicode('🙂')", "unicode(123)",
        "unicode(char(0,65))", "unicode(char(1114111))", "unicode(char(65534))",
        "unicode(char(65535))", "instr(X'FF','')",
        "unhex(char(65534)||'41',char(65533))")
    for raw in [bytes([i]) for i in range(256)] + [
            bytes.fromhex(h) for h in ["c0af", "eda080", "efbfbf", "f4908080", "ff8080808080", "c28080", "cbbeb9a28f89934749", "ffbfbfbfbfbfbf"]]:
        add("unicode-bytes", f"unicode({blob_literal(raw)})")
    add("zeroblob", "zeroblob(NULL)", "zeroblob(-1)", "zeroblob('3.5')", "zeroblob(16)")
    add("sign", "sign('1x')", "sign(' 1.5 ')", "sign('abc')", "sign(X'31')",
        "sign('1e999')", "sign('-1e999')", "sign('-0.0')", f"sign({text_literal('1' + chr(0) + 'x')})")
    add("quote", "quote('O''Brien')", "quote(1e999)", "quote(-1e999)", "quote(-0.0)")
    for name in ["min", "max"]:
        for values_ in ["1,1.0", "1.0,1", "1,NULL,2", "'9',3,X'00'", "'a','A'", "-0.0,0.0"]:
            add("minmax", f"{name}({values_})")
    rng = random.Random(seed)
    for _ in range(count):
        source = "".join(rng.choice("abxy áβ🙂\x00\t'") for _ in range(rng.randrange(0, 35)))
        needle = "".join(rng.choice("abáβ🙂\x00") for _ in range(rng.randrange(0, 5)))
        replacement = "".join(rng.choice("XYá🙂\x00") for _ in range(rng.randrange(0, 5)))
        a, b, c = map(text_literal, [source, needle, replacement])
        start, length = rng.randrange(-40, 41), rng.randrange(-40, 41)
        raw = bytes(rng.randrange(256) for _ in range(rng.randrange(20)))
        add("seeded-text", f"substr({a},{start},{length})", f"instr({a},{b})",
            f"replace({a},{b},{c})", f"trim({a},{b})", f"quote({a})", f"concat_ws({c},{a},NULL,{b})")
        add("seeded-blob", f"hex({blob_literal(raw)})", f"unhex('{raw.hex()}')",
            f"substr({blob_literal(raw)},{start},{length})", f"unicode({blob_literal(raw)})")
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=pathlib.Path, default=ROOT / ".lake/build/bin/sqleanite")
    parser.add_argument("--sqlite", default="/usr/bin/sqlite3")
    parser.add_argument("--seed", type=int, default=353410)
    parser.add_argument("--random-cases", type=int, default=120)
    parser.add_argument("--output", type=pathlib.Path)
    args = parser.parse_args()
    cases = corpus(args.seed, args.random_cases)
    with tempfile.TemporaryDirectory(prefix="sqleanite-text-") as tmp:
        cwd = pathlib.Path(tmp)
        sql = "CREATE TABLE t(id INTEGER PRIMARY KEY,v); BEGIN;\n" + "\n".join(
            f"INSERT INTO t VALUES({i},{expression});" for i, (_, expression) in enumerate(cases, 1)) + "\nCOMMIT;"
        actual, expected = scalar.run(args, cwd, sql)
        if actual.returncode or expected.returncode:
            raise RuntimeError(f"Lean: {actual.stdout}{actual.stderr}\nSQLite: {expected.stdout}{expected.stderr}")
        rows, reference = scalar.observe(cwd / "lean.db"), scalar.observe(cwd / "sqlite.db")
        assert len(rows) == len(reference) == len(cases)
        failures = [dict(id=i, group=cases[i-1][0], expression=cases[i-1][1], lean=a, sqlite=b)
                    for i, (a, b) in enumerate(zip(rows, reference), 1) if a != b]
        for sql in ["UPDATE t SET v=substr('árvíz',2,3) WHERE id=1;",
                    "CREATE INDEX ix ON t(v); SELECT id FROM t WHERE v=substr('árvíz',2,3) ORDER BY id;",
                    "SELECT hex(unhex('61 62',' ')),unicode('🙂'),typeof(min(1,1.0));"]:
            actual, expected = scalar.run(args, cwd, sql)
            assert actual.returncode == expected.returncode == 0, (sql, actual.stderr, expected.stderr)
            assert actual.stdout == expected.stdout, (sql, actual.stdout, expected.stdout)
        assert scalar.observe(cwd / "lean.db") == scalar.observe(cwd / "sqlite.db") or failures
        before = scalar.observe(cwd / "lean.db")
        errors = ["hex()", "hex(1,2)", "unhex()", "substr('a')", "substr('a',1,2,3)",
                  "instr('a')", "trim()", "replace('a','b')", "concat()", "concat_ws('-')",
                  "unicode()", "quote(1,2)", "sign()", "zeroblob()", "min()", "max()",
                  "coalesce(1,hex())", "CASE WHEN 1 THEN 1 ELSE substr('a') END", "coalesce(1,unknown_function())"]
        for expr in errors:
            actual, expected = scalar.run(args, cwd, f"INSERT INTO t VALUES(999999,{expr});")
            assert actual.returncode != 0 and expected.returncode != 0, expr
            assert scalar.observe(cwd / "lean.db") == before, expr
        declared = ["length(zeroblob(1000000))"]
        for expr in declared:
            actual, _ = scalar.run(args, cwd, f"INSERT INTO t VALUES(999999,{expr});")
            assert actual.returncode != 0, expr
            assert scalar.observe(cwd / "lean.db") == before, expr
        digest = hashlib.sha256()
        for path in sorted((ROOT / "SQLeanite").rglob("*.lean")) + [ROOT / "Main.lean"]:
            digest.update(str(path.relative_to(ROOT)).encode() + b"\0" + path.read_bytes())
        report = dict(implementation_sha256=digest.hexdigest(),
                      harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                      seed=args.seed, random_cases=args.random_cases, cases=len(cases),
                      failures=failures, matching_errors=len(errors), declared_rejections=declared,
                      sqlite_version=subprocess.check_output([args.sqlite, "--version"], text=True).strip(),
                      comparison="storage class, exact binary64 bits, raw TEXT/BLOB bytes; integrity_check")
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))
        return bool(failures)


if __name__ == "__main__":
    raise SystemExit(main())
