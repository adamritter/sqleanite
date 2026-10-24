#!/usr/bin/env python3
"""Exercise declared types, persistence, affinity and index lookup against C SQLite."""
import argparse
import json
import pathlib
import sqlite3
import struct
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
TYPES = ["", "TEXT", "INTEGER", "REAL", "NUMERIC", "BLOB", "VARCHAR(12)",
         "DOUBLE PRECISION", "FLOATING POINT", "STRING", '"custom INT type"',
         '"a""b TEXT type"']
VALUES = ["NULL", "0", "1", "-1", "9223372036854775807", "-9223372036854775808",
          "1.0", "-0.0", "1.5", "1e999", "-1e999", "9007199254740992.0",
          "'001'", "'12'", "'1.0'", "'3e0'", "'1.5'", "'0x10'", "'abc'", "'12x'",
          "''", "'árvíz'", "'  -12  '", "'9223372036854775807'", "'9223372036854775808'",
          "'-9223372036854775808'", "'-9223372036854775809'", "'1e999'", "'1e-999'",
          "'2251799813685248.0'", "'4503599627370496.0'", "X'3132'", "X'00FF'",
          "CAST(X'31320078' AS TEXT)", "CAST(X'313200' AS TEXT)",
          "CAST(X'31327800' AS TEXT)", "CAST(X'2031320020' AS TEXT)"]


def command(args, engine, database, sql, work):
    if engine == "lean":
        script = work / "query.sql"
        script.write_text(sql)
        return subprocess.run([str(args.lean), "--verified-file", str(database), str(script)],
                              capture_output=True, timeout=120)
    return subprocess.run([args.sqlite, "-batch", "-bail", str(database)], input=sql.encode(),
                          capture_output=True, timeout=120)


def observation(path):
    with sqlite3.connect(path) as db:
        db.text_factory = bytes
        integrity = db.execute("PRAGMA integrity_check").fetchall()
        assert integrity == [(b"ok",)], (str(path), integrity)
        tables = db.execute("SELECT name FROM sqlite_schema WHERE type='table' ORDER BY name").fetchall()
        result = {}
        for (raw_name,) in tables:
            name = raw_name.decode()
            columns = db.execute(f'PRAGMA table_info("{name}")').fetchall()
            type_query = ",".join(f'typeof("{c[1].decode()}")' for c in columns)
            rows = db.execute(f'SELECT *,{type_query} FROM "{name}" ORDER BY 1').fetchall()
            result[name] = (columns, rows)
        return result


def printable(value):
    if isinstance(value, bytes):
        return {"bytes": value.hex()}
    if isinstance(value, float):
        return {"binary64": struct.pack(">d", value).hex()}
    if isinstance(value, (list, tuple)):
        return [printable(x) for x in value]
    if isinstance(value, dict):
        return {k: printable(v) for k, v in value.items()}
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=pathlib.Path, default=ROOT / ".lake/build/bin/sqleanite")
    parser.add_argument("--sqlite", default="/usr/bin/sqlite3")
    parser.add_argument("--output", type=pathlib.Path)
    args = parser.parse_args()
    queries = 0
    with tempfile.TemporaryDirectory(prefix="sqleanite-affinity-") as tmp:
        work = pathlib.Path(tmp)
        lean, reference = work / "lean.db", work / "sqlite.db"

        def both(sql):
            nonlocal queries
            a = command(args, "lean", lean, sql, work)
            b = command(args, "sqlite", reference, sql, work)
            assert a.returncode == b.returncode == 0, (sql[:400], a.stderr.decode(), b.stderr.decode())
            assert a.stdout == b.stdout, (sql[:400], a.stdout, b.stdout)
            queries += sql.count("SELECT") - sql.count("SELECT 'affinity-query-")

        setup = []
        for table, kind in enumerate(TYPES):
            setup.append(f"CREATE TABLE t{table}(id INTEGER PRIMARY KEY,v {kind});")
            setup.extend(f"INSERT INTO t{table} VALUES({key},{value});"
                         for key, value in enumerate(VALUES, 1))
        both("BEGIN;\n" + "\n".join(setup) + "\nCOMMIT;")
        a, b = printable(observation(lean)), printable(observation(reference))
        assert a == b, json.dumps({k: {"lean": a[k], "sqlite": b[k]} for k in a if a[k] != b[k]}, indent=2)

        def probe():
            sql = []
            for table in range(len(TYPES)):
                for value in ["1", "'001'", "'12'", "1.5", "'1.5'", "NULL", "X'3132'", "'abc'"]:
                    for op in ["=", "!=", "<", ">=", "<=", ">"]:
                        sql.append(f"SELECT id FROM t{table} WHERE v {op} {value} ORDER BY id;")
                        sql.append(f"SELECT id FROM t{table} WHERE {value} {op} v ORDER BY id;")
                sql.append(f"SELECT id FROM t{table} WHERE v IS NULL;")
                # Project a value that requires REAL reconstruction on C-written files.
                sql.append(f"SELECT id,v FROM t{table} WHERE id=7;")
            # Distinguish each result set, including empty results, so a missing
            # row cannot be hidden by an extra row in the next query.
            return "\n".join(query + f"\nSELECT 'affinity-query-{index}';"
                             for index, query in enumerate(sql))

        both(probe())
        both("\n".join(f"CREATE INDEX i{t} ON t{t}(v);" for t in range(len(TYPES))))
        both(probe())
        both("\n".join(f"UPDATE t{t} SET v='12.0' WHERE id=3; REPLACE INTO t{t}(v,id) VALUES(1.5,4);"
                       for t in range(len(TYPES))))
        assert printable(observation(lean)) == printable(observation(reference))
        both(probe())

        both("CREATE TABLE pk(k TEXT PRIMARY KEY,v REAL); INSERT INTO pk VALUES(12,'5.0'); "
             "SELECT k,v FROM pk WHERE k=12; SELECT k,v FROM pk WHERE k='12';")
        both("CREATE TABLE ipk(id INTEGER PRIMARY KEY,v TEXT); INSERT INTO ipk VALUES('12.0',7); "
             "SELECT id,v FROM ipk WHERE id='12';")
        both("CREATE TABLE nn(id INTEGER PRIMARY KEY,v NUMERIC NOT NULL); INSERT INTO nn VALUES(1,'3e0');")
        both("SELECT t1.id,t3.id FROM t1 INNER JOIN t3 ON t1.id=t3.id WHERE t1.v=12 ORDER BY t1.id;")
        assert printable(observation(lean)) == printable(observation(reference))

        # The independently C-created file must also be readable after index creation.
        query = probe()
        a = command(args, "lean", reference, query, work)
        b = command(args, "sqlite", reference, query, work)
        assert a.returncode == b.returncode == 0, (a.stderr, b.stderr)
        assert a.stdout == b.stdout, "reverse read differs"
        queries += query.count("SELECT") - query.count("SELECT 'affinity-query-")

        # Modify an independently C-created/indexed image using the Lean writer.
        native = work / "native.db"
        with sqlite3.connect(reference) as source, sqlite3.connect(native) as target:
            source.backup(target)
        mutation = "UPDATE t3 SET v='8.0' WHERE id=7; INSERT INTO t1 VALUES(100,42);"
        a = command(args, "lean", native, mutation, work)
        b = command(args, "sqlite", reference, mutation, work)
        assert a.returncode == b.returncode == 0, (a.stderr, b.stderr)
        assert printable(observation(native)) == printable(observation(reference)), "reverse write differs"
        # Keep the two forward fixtures synchronized for the following failures.
        a = command(args, "lean", lean, mutation, work)
        assert a.returncode == 0, a.stderr

        before = printable(observation(lean))
        for sql in ["INSERT INTO pk VALUES('12',9);", "INSERT INTO ipk VALUES('12x',9);",
                    "UPDATE nn SET v=NULL;", "INSERT INTO nn VALUES(2,NULL);"]:
            a = command(args, "lean", lean, sql, work)
            b = command(args, "sqlite", reference, sql, work)
            assert a.returncode != 0 and b.returncode != 0, (sql, a.stderr, b.stderr)
            assert printable(observation(lean)) == before, "failed statement mutated data"

        # These mixed-affinity comparisons need a general row expression operand.
        for sql in ["SELECT id FROM t1 WHERE v=CAST(12 AS INTEGER);",
                    "SELECT t1.id FROM t1 INNER JOIN t2 ON t1.v=t2.v;"]:
            a = command(args, "lean", lean, sql, work)
            assert a.returncode != 0 and b"conversion" in a.stderr, (sql, a.stderr)

        report = {"typed_insert_values": len(TYPES) * len(VALUES), "select_queries": queries,
                  "declared_types": TYPES, "expected_write_errors": 4,
                  "unsupported_mixed_affinity_queries": 2, "reverse_write_checks": 1, "mismatches": 0,
                  "sqlite_version": subprocess.check_output([args.sqlite, "--version"], text=True).strip()}
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
