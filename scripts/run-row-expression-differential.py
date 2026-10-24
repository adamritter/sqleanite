#!/usr/bin/env python3
"""Compare row-dependent production SELECTs to pinned C SQLite.

Checks storage classes and hex-encoded value/quote renderings in query output,
plus byte-identical database state after reads. This is query-output evidence,
not an exact binary64-bit comparison of arbitrary SELECT results.
"""
import argparse
import hashlib
import json
import pathlib
import random
import sqlite3
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]


def text(value):
    return "CAST(X'" + value.encode().hex() + "' AS TEXT)"


def run(args, cwd, source):
    query = cwd / "query.sql"
    query.write_text(source)
    actual = subprocess.run([str(args.lean), "--verified-file", str(cwd / "lean.db"), str(query)],
                            capture_output=True, text=True, timeout=120)
    expected = subprocess.run([args.sqlite, "-batch", "-bail", str(cwd / "sqlite.db")],
                              input=source, capture_output=True, text=True, timeout=120)
    return actual, expected


def cases(seed, count):
    rng = random.Random(seed)
    inserts = ["CREATE TABLE t(id INTEGER PRIMARY KEY,i INTEGER,n NUMERIC,r REAL,s TEXT,b BLOB,u);", "BEGIN;"]
    for key in range(1, 81):
        i = rng.randint(-100000, 100000)
        n = rng.choice(["NULL", "'2'", "'2.5'", "'x'", "0", "-3.5"])
        s = text(rng.choice(["hello", "árvíz🙂", "2", "'quoted'", "a\x00b", "", "  xyz  "]))
        blob = "X'" + bytes(rng.randrange(256) for _ in range(3)).hex() + "'"
        u = rng.choice(["NULL", "1", "1.0", "'1'", "2", "0.0", "-0.0", "X'31'"])
        inserts.append(f"INSERT INTO t VALUES({key},{i},{n},{i}/7.0,{s},{blob},{u});")
    inserts.extend(["COMMIT;", "CREATE INDEX ti ON t(i);", "CREATE TABLE empty(id INTEGER PRIMARY KEY,v);"])
    expressions = ["i+1", "i*n", "r/3", "s+0", "CAST(s AS INTEGER)", "CAST(i AS TEXT)",
                   "upper(s)", "substr(s,2,-1)", "hex(b)", "instr(s,'🙂')", "replace(s,'l','XX')",
                   "coalesce(n,i)", "iif(n,n,42)", "CASE n WHEN '2' THEN 'yes' ELSE 'no' END",
                   "n='2'", "+n='2'", "s=2", "s=CAST(2 AS INT)", "n IS NULL", "-r", "~i",
                   "min(n,i)", "max(n,i)", "n||s", "unicode(b)", "length(b)", "sign(n)",
                   "quote(u)", "u=1.0", "NULL+i", "id+rowid", "t.id+t.i"]
    for _ in range(count):
        left = rng.choice(["i", "n", "r", "s", "u", "id"])
        right = rng.choice([str(rng.randrange(-200, 200)), "i", "n", "s", "NULL", "'2'", "2.0"])
        op = rng.choice(["+", "-", "*", "/", "%", "=", "IS", "<", "||", "&"])
        expressions.append(f"({left}) {op} ({right})")
    queries = []
    for expression in expressions:
        queries.append(f"SELECT id,typeof({expression}),hex({expression}),hex(quote({expression})) FROM t ORDER BY id;")
    queries += [
        "SELECT upper(x.s),x.i+2 FROM t AS x WHERE id>=77 ORDER BY id DESC LIMIT 2;",
        "SELECT hex(s),i+2 FROM t WHERE id=1;",
        "SELECT max(i,2) FROM t WHERE id<4 ORDER BY id;",
        "SELECT upper(v),* FROM empty;",
        "SELECT abs(-9223372036854775808)+id FROM t LIMIT 0;",
        "SELECT abs(-9223372036854775808)+id FROM t WHERE id<0;",
        "SELECT DISTINCT +u FROM t;",
        "SELECT DISTINCT u,+u FROM t ORDER BY u DESC LIMIT 4;",
        "SELECT DISTINCT +u FROM t LIMIT 3;",
        "SELECT DISTINCT +u FROM t ORDER BY id DESC LIMIT 4;",
        "SELECT DISTINCT abs(-9223372036854775808)+id FROM t LIMIT 0;",
        "SELECT id+1 FROM t WHERE id=1 UNION ALL SELECT id+1 FROM t WHERE id=2;",
        "SELECT * ,v+1 FROM empty;",
    ]
    inserts.extend(["CREATE TABLE duplicates(id INTEGER PRIMARY KEY,v INTEGER,label TEXT);", "BEGIN;"])
    for key in range(1, 101):
        v = rng.choice(["NULL"] + [str(n) for n in range(-5, 6)])
        label = text(rng.choice(["a", "b", "árvíz"]))
        inserts.append(f"INSERT INTO duplicates VALUES({key},{v},{label});")
    inserts.extend(["COMMIT;", "CREATE INDEX duplicate_v ON duplicates(v);"])
    for limit in [0, 1, 2, 5, 20, 200]:
        for direction in ["ASC", "DESC"]:
            for where in ["", " WHERE v>=0", " WHERE id>30", " WHERE id<0"]:
                queries.append(f"SELECT DISTINCT v FROM duplicates{where} ORDER BY v {direction} LIMIT {limit};")
            queries.append(f"SELECT DISTINCT v,label FROM duplicates ORDER BY v {direction},label LIMIT {limit};")
    return "\n".join(inserts), queries


def split_results(output):
    parts = {}
    key = None
    for line in output.splitlines():
        if line.startswith("@@case:"):
            key = int(line.removeprefix("@@case:"))
            parts[key] = []
        elif key is not None:
            parts[key].append(line)
        else:
            raise AssertionError(f"unmarked result: {line!r}")
    return parts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=pathlib.Path, default=ROOT / ".lake/build/bin/sqleanite")
    parser.add_argument("--sqlite", default="/usr/bin/sqlite3")
    parser.add_argument("--seed", type=int, default=353420)
    parser.add_argument("--random-cases", type=int, default=100)
    parser.add_argument("--output", type=pathlib.Path)
    args = parser.parse_args()
    setup, queries = cases(args.seed, args.random_cases)
    with tempfile.TemporaryDirectory(prefix="sqleanite-rowexpr-") as tmp:
        cwd = pathlib.Path(tmp)
        actual, expected = run(args, cwd, setup)
        assert actual.returncode == expected.returncode == 0, (actual.stderr, expected.stderr)
        before = (cwd / "lean.db").read_bytes()
        source = "\n".join(f"SELECT '@@case:{i}';\n{query}" for i, query in enumerate(queries))
        actual, expected = run(args, cwd, source)
        assert actual.returncode == expected.returncode == 0, (actual.stdout[-2000:], actual.stderr, expected.stderr)
        rows, reference = split_results(actual.stdout), split_results(expected.stdout)
        assert set(rows) == set(reference) == set(range(len(queries)))
        failures = [dict(index=i, sql=queries[i], lean=rows[i], sqlite=reference[i])
                    for i in range(len(queries)) if rows[i] != reference[i]]
        assert (cwd / "lean.db").read_bytes() == before, "SELECT changed the stored database"
        errors = ["SELECT missing+1 FROM empty;", "SELECT missing+1 FROM t LIMIT 0;",
                  "SELECT coalesce(1,missing) FROM empty;", "SELECT coalesce(1,unknown_function(i)) FROM t LIMIT 0;",
                  "SELECT wrong.i+1 FROM t;", "SELECT t.i+1 FROM t AS alias;",
                  "SELECT abs(-9223372036854775808)+id FROM t LIMIT 1;",
                  "SELECT substr(s) FROM t LIMIT 0;"]
        for query in errors:
            actual, expected = run(args, cwd, query)
            assert actual.returncode != 0 and expected.returncode != 0, (query, actual.stdout, expected.stdout)
            assert (cwd / "lean.db").read_bytes() == before, query
        declared = []
        rendering_sql = "SELECT 3.0;\nSELECT NULL;\nSELECT '';\nSELECT char(65,0,66);\nSELECT 1 WHERE 0;\n"
        rendering_file = cwd / "render.sql"
        rendering_file.write_text(rendering_sql)
        reference_render = subprocess.run([args.sqlite, "-batch", "-bail", ":memory:"],
            input=rendering_sql, text=True, capture_output=True, timeout=120)
        assert reference_render.returncode == 0
        assert reference_render.stdout == "3.0\n\n\nA\n"
        modes = ["--verified-file", "--verified-wal-file", "--verified-file-timed"]
        for mode in modes:
            rendered = subprocess.run([str(args.lean), mode, str(cwd / (mode + ".db")), str(rendering_file)],
                text=True, capture_output=True, timeout=120)
            assert rendered.returncode == 0, (mode, rendered.stderr)
            assert rendered.stdout == reference_render.stdout, (mode, rendered.stdout, reference_render.stdout)
        # Regression for the previously reproduced direct-column LIMIT bug.
        query = "SELECT DISTINCT v FROM d ORDER BY id LIMIT 2;"
        setup = "CREATE TABLE d(id INTEGER PRIMARY KEY,v);INSERT INTO d VALUES(1,1),(2,1),(3,2);"
        actual, expected = run(args, cwd, setup)
        assert actual.returncode == expected.returncode == 0, (actual.stderr, expected.stderr)
        actual, expected = run(args, cwd, query)
        assert actual.returncode == expected.returncode == 0, (actual.stderr, expected.stderr)
        assert actual.stdout == expected.stdout == "1\n2\n", (query, actual.stdout, expected.stdout)
        distinct_regression = dict(sql=query, result=actual.stdout, matches_sqlite=True)
        # Regression: INTEGER and equal REAL keys collapse without changing
        # the first original representative's storage class.
        setup = "CREATE TABLE mixed(id INTEGER PRIMARY KEY,v);INSERT INTO mixed VALUES(1,1),(2,1.0);"
        actual, expected = run(args, cwd, setup)
        assert actual.returncode == expected.returncode == 0, (actual.stderr, expected.stderr)
        mixed_query = "SELECT DISTINCT v FROM mixed;"
        actual, expected = run(args, cwd, mixed_query)
        assert actual.returncode == expected.returncode == 0, (actual.stderr, expected.stderr)
        if actual.stdout != expected.stdout:
            failures.append(dict(sql=mixed_query, lean=actual.stdout, sqlite=expected.stdout))
        numeric_regression = dict(sql=mixed_query, lean=actual.stdout, sqlite=expected.stdout,
                                  matches_sqlite=actual.stdout == expected.stdout)
        with sqlite3.connect(cwd / "lean.db") as db:
            assert db.execute("PRAGMA integrity_check").fetchone() == ("ok",)
        digest = hashlib.sha256()
        for path in sorted((ROOT / "SQLeanite").rglob("*.lean")) + [ROOT / "Main.lean"]:
            digest.update(str(path.relative_to(ROOT)).encode() + b"\0" + path.read_bytes())
        report = dict(seed=args.seed, random_cases=args.random_cases, queries=len(queries),
                      result_rows=sum(map(len, rows.values())), matching_errors=len(errors), declared_rejections=declared, failures=failures,
                      distinct_limit_regression=distinct_regression, cli_render_modes=modes,
                      numeric_distinct_regression=numeric_regression, implementation_sha256=digest.hexdigest(),
                      comparison="query storage classes, hex value/quote renderings; SELECT file-state preservation",
                      sqlite_version=subprocess.check_output([args.sqlite, "--version"], text=True).strip())
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))
        return bool(failures)


if __name__ == "__main__":
    raise SystemExit(main())
