#!/usr/bin/env python3
"""Compare numeric DISTINCT through the production CLI with independent SQLite.

Checks first representative rendering, multiplicity, LIMIT, index/reopen paths,
column permutations and unchanged files. BLOB rendering is outside this suite;
Tests.lean checks BLOB/TEXT separation as typed Core values. This is not a
whole-SQLite compatibility percentage or an exact SELECT binary64-bit metric.
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


def pairs(seed, count):
    rng = random.Random(seed)
    out = [("1", "1.0"), ("1.0", "1"), ("0", "-0.0"), ("-0.0", "0.0"),
           ("NULL", "NULL"), ("1", "'1'"), ("1.5", "1.5"),
           ("9007199254740992", "9007199254740992.0"),
           ("9007199254740993", "9007199254740992.0"),
           ("-9223372036854775808", "-9223372036854775808.0"),
           ("9223372036854775807", "9223372036854775808.0"),
           ("1e999", "1e999"), ("-1e999", "-1e999"), ("5e-324", "0"),
           ("2.2250738585072014e-308", "2.2250738585072014e-308")]
    for _ in range(count):
        if rng.randrange(2):
            integer = rng.randrange(-(2**63), 2**63)
        else:
            exponent = rng.randrange(64)
            integer = max(-(2**63), min(2**63-1, rng.choice([-1, 1]) * 2**exponent + rng.randrange(-3, 4)))
        real = repr(float(integer))
        choices = [str(integer), real, str(integer) + ".0", "'" + str(integer) + "'", "NULL"]
        a, b = str(integer), rng.choice(choices)
        if rng.randrange(2):
            a, b = b, a
        out.append((a, b))
    return out


def execute(args, directory, sql):
    source = directory / "query.sql"
    source.write_text(sql)
    lean = subprocess.run([str(args.lean), "--verified-file", str(directory / "lean.db"), str(source)],
                          capture_output=True, text=True, timeout=120)
    reference = subprocess.run([args.sqlite, "-batch", "-bail", str(directory / "sqlite.db")],
                               input=sql, capture_output=True, text=True, timeout=120)
    assert lean.returncode == reference.returncode == 0, (lean.stderr, reference.stderr)
    return lean.stdout, reference.stdout


def split_results(stdout):
    output, key = {}, None
    for line in stdout.splitlines():
        if line.startswith("@@case:"):
            key = int(line.removeprefix("@@case:"))
            output[key] = []
        else:
            assert key is not None, line
            output[key].append(line)
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=pathlib.Path, default=ROOT / ".lake/build/bin/sqleanite")
    parser.add_argument("--sqlite", default="/usr/bin/sqlite3")
    parser.add_argument("--seed", type=int, default=353430)
    parser.add_argument("--random-cases", type=int, default=100)
    parser.add_argument("--output", type=pathlib.Path)
    args = parser.parse_args()
    inputs = pairs(args.seed, args.random_cases)
    setup = ["CREATE TABLE t(id INTEGER PRIMARY KEY,g INTEGER,v,tag TEXT);", "BEGIN;"]
    queries = []
    for group, (a, b) in enumerate(inputs):
        setup += [f"INSERT INTO t VALUES({2*group+1},{group},{a},'same'),({2*group+2},{group},{b},'same');"]
        for projection in ["v", "+v", "v,tag", "tag,v"]:
            for limit in ["", " LIMIT 1", " LIMIT 2"]:
                queries.append(f"SELECT DISTINCT {projection} FROM t WHERE g={group}{limit};")
        # Ordering ties keep the first representation; LIMIT is applied only
        # after duplicate elimination. Large unequal integer/REALs must stay apart.
        queries += [f"SELECT DISTINCT v FROM t WHERE g={group} ORDER BY v {direction};"
                    for direction in ["ASC", "DESC"]]
    setup += ["COMMIT;"]
    failures, phases = [], []
    with tempfile.TemporaryDirectory(prefix="sqleanite-distinct-") as tmp:
        directory = pathlib.Path(tmp)
        execute(args, directory, "\n".join(setup))
        marked = "\n".join(f"SELECT '@@case:{i}';\n{sql}" for i, sql in enumerate(queries))
        for phase in ["unindexed-reopen", "indexed-reopen"]:
            if phase == "indexed-reopen":
                execute(args, directory, "CREATE INDEX tg ON t(g);")
            before = (directory / "lean.db").read_bytes()
            actual, expected = map(split_results, execute(args, directory, marked))
            assert set(actual) == set(expected) == set(range(len(queries)))
            for i, sql in enumerate(queries):
                if actual[i] != expected[i]:
                    failures.append(dict(phase=phase, sql=sql, lean=actual[i], sqlite=expected[i]))
            assert (directory / "lean.db").read_bytes() == before, "SELECT modified database"
            with sqlite3.connect(directory / "lean.db") as db:
                assert db.execute("PRAGMA integrity_check").fetchone() == ("ok",)
            phases.append(dict(name=phase, queries=len(queries), result_rows=sum(map(len, actual.values()))))
    digest = hashlib.sha256()
    for path in sorted((ROOT / "SQLeanite").rglob("*.lean")) + [ROOT / "Main.lean"]:
        digest.update(str(path.relative_to(ROOT)).encode() + b"\0" + path.read_bytes())
    report = dict(seed=args.seed, random_cases=args.random_cases, input_pairs=len(inputs), phases=phases,
                  queries=sum(p["queries"] for p in phases), failures=failures,
                  comparison="query-output multiplicity and numeric representative rendering; read file-state preservation",
                  implementation_sha256=digest.hexdigest(),
                  executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
                  harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                  sqlite_version=subprocess.check_output([args.sqlite, "--version"], text=True).strip())
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return bool(failures)


if __name__ == "__main__":
    raise SystemExit(main())
