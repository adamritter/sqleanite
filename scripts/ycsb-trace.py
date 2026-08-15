#!/usr/bin/env python3
"""Generate a deterministic YCSB operation trace as two SQL files.

The workload parameters and generators follow VeriBetrKV's OSDI'20 artifact
(`secure-foundations/veribetrkv-osdi2020`, `ycsb/*.spec`) rather than the stock
YCSB defaults, so our numbers are comparable to published ones. Their specs use
`fieldcount=1, fieldlength=512` -- one 512-byte field, not ten 100-byte fields.

The zipfian, scrambled-zipfian and skewed-latest generators are ports of YCSB's
Java implementations (`ZipfianGenerator`, `ScrambledZipfianGenerator`,
`SkewedLatestGenerator`) so the key-selection skew matches. Everything is seeded
so both engines replay an identical trace.

Emits:
  <out>/load.sql  exact paper schema and `recordcount` inserts in one transaction
  <out>/run.sql   `operationcount` operations in the workload's mix

Usage:
  ycsb-trace.py --workload A --records 1000 --ops 100 --out DIR [--seed N]
"""

import argparse
import os
import random
import sys

# --- YCSB generators -------------------------------------------------------

FNV64_OFFSET = 0xCBF29CE484222325
FNV64_PRIME = 0x100000001B3


def fnvhash64(value):
    """YCSB's `Utils.fnvhash64`, used by ScrambledZipfianGenerator."""
    h = FNV64_OFFSET
    for _ in range(8):
        h ^= value & 0xFF
        h = (h * FNV64_PRIME) & 0xFFFFFFFFFFFFFFFF
        value >>= 8
    return h


class Zipfian:
    """YCSB's ZipfianGenerator (Gray et al.), default constant 0.99.

    `zetan` is computed by summation, which is O(items). That is a few seconds
    at 10M and is done once per trace, so it is not worth approximating.
    """

    def __init__(self, items, theta=0.99):
        self.items = items
        self.theta = theta
        self.zetan = sum(1.0 / pow(i, theta) for i in range(1, items + 1))
        self.zeta2 = 1.0 + pow(0.5, theta)
        self.alpha = 1.0 / (1.0 - theta)
        self.eta = (1.0 - pow(2.0 / items, 1.0 - theta)) / (
            1.0 - self.zeta2 / self.zetan
        )

    def next(self, rng):
        u = rng.random()
        uz = u * self.zetan
        if uz < 1.0:
            return 0
        if uz < 1.0 + pow(0.5, self.theta):
            return 1
        return int(self.items * pow(self.eta * u - self.eta + 1.0, self.alpha))


class ScrambledZipfian:
    """`requestdistribution=zipfian` in YCSB: zipfian then hash-scattered, so
    the hot keys are spread across the key space rather than clustered."""

    def __init__(self, items, theta=0.99):
        self.items = items
        self.gen = Zipfian(items, theta)

    def next(self, rng):
        return fnvhash64(self.gen.next(rng)) % self.items


class SkewedLatest:
    """`requestdistribution=latest`: zipfian over recency, so the most
    recently inserted keys are the hottest."""

    def __init__(self, items, theta=0.99):
        self.items = items
        self.gen = Zipfian(items, theta)

    def next(self, rng, maxkey):
        return max(0, maxkey - self.gen.next(rng))


class Uniform:
    def __init__(self, items):
        self.items = items

    def next(self, rng):
        return rng.randrange(self.items)


# --- workload table (VeriBetrKV's specs) -----------------------------------
# read, update, scan, insert, readmodifywrite, distribution
WORKLOADS = {
    "A": (0.5, 0.5, 0.0, 0.0, 0.0, "zipfian"),
    "B": (0.95, 0.05, 0.0, 0.0, 0.0, "zipfian"),
    "C": (1.0, 0.0, 0.0, 0.0, 0.0, "zipfian"),
    "D": (0.95, 0.0, 0.0, 0.05, 0.0, "latest"),
    "E": (0.0, 0.0, 0.95, 0.05, 0.0, "zipfian"),
    "F": (0.5, 0.0, 0.0, 0.0, 0.5, "zipfian"),
    "Cuniform": (1.0, 0.0, 0.0, 0.0, 0.0, "uniform"),
}

FIELD_LENGTH = 512  # VeriBetrKV fieldlength; --field-length overrides for triage
MAX_SCAN_LENGTH = 100


def keyname(index):
    """YCSB key format: `user` followed by the hashed key index."""
    return "user%d" % fnvhash64(index)


def fieldvalue(rng, length=FIELD_LENGTH):
    # YCSB fills fields with random printable bytes. A single repeated
    # character would compress the page cache in a way real data does not,
    # so use varied ASCII, seeded.
    return "".join(chr(rng.randrange(97, 123)) for _ in range(length))


def quote(text):
    return "'" + text.replace("'", "''") + "'"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workload", required=True, choices=sorted(WORKLOADS))
    parser.add_argument("--records", type=int, required=True)
    parser.add_argument("--ops", type=int, required=True)
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=20260814)
    parser.add_argument("--insert-batch", type=int, default=1,
                        help="rows per INSERT in the load phase. 1 matches "
                             "YCSB one-record-at-a-time. Larger values exist "
                             "only because the batch SQL path overflows the "
                             "stack somewhere between 50k and 60k statements "
                             "in one invocation; batching keeps the same rows "
                             "and the same data, and both engines replay the "
                             "identical script")
    parser.add_argument("--field-length", type=int, default=FIELD_LENGTH,
                        help="512 matches VeriBetrKV; lower values are a "
                             "reduced-fidelity triage mode, not paper numbers")
    args = parser.parse_args()

    if args.records < 1:
        sys.exit("--records must be positive")
    read_p, update_p, scan_p, insert_p, rmw_p, dist = WORKLOADS[args.workload]

    os.makedirs(args.out, exist_ok=True)
    rng = random.Random(args.seed)

    # --- load phase ---
    # One transaction, matching the bulk-load shape their driver uses.
    load_path = os.path.join(args.out, "load.sql")
    with open(load_path, "w") as out:
        # Preserve the benchmark's string-key schema literally. In SQLite a
        # TEXT PRIMARY KEY is backed by an implicit unique index on a rowid
        # table; Core supports and certifies that physical representation.
        out.write(
            "CREATE TABLE usertable (ycsb_key TEXT PRIMARY KEY, field0 TEXT);\n"
        )
        out.write("BEGIN;\n")
        batch = max(1, args.insert_batch)
        pending = []
        for i in range(args.records):
            pending.append(
                "(%s,%s)"
                % (quote(keyname(i)), quote(fieldvalue(rng, args.field_length)))
            )
            if len(pending) == batch:
                out.write("INSERT INTO usertable VALUES %s;\n" % ",".join(pending))
                pending = []
        if pending:
            out.write("INSERT INTO usertable VALUES %s;\n" % ",".join(pending))
        out.write("COMMIT;\n")

    # --- run phase ---
    if dist == "zipfian":
        chooser = ScrambledZipfian(args.records)
    elif dist == "uniform":
        chooser = Uniform(args.records)
    else:
        chooser = SkewedLatest(args.records)

    thresholds = []
    acc = 0.0
    for name, weight in (
        ("read", read_p),
        ("update", update_p),
        ("scan", scan_p),
        ("insert", insert_p),
        ("rmw", rmw_p),
    ):
        if weight > 0.0:
            acc += weight
            thresholds.append((acc, name))

    run_path = os.path.join(args.out, "run.sql")
    next_key = args.records
    with open(run_path, "w") as out:
        for _ in range(args.ops):
            pick = rng.random()
            op = thresholds[-1][1]
            for bound, name in thresholds:
                if pick < bound:
                    op = name
                    break

            if op == "insert":
                out.write(
                    "INSERT INTO usertable VALUES(%s,%s);\n"
                    % (quote(keyname(next_key)), quote(fieldvalue(rng, args.field_length)))
                )
                next_key += 1
                continue

            if dist == "latest":
                index = chooser.next(rng, next_key - 1)
            else:
                index = chooser.next(rng)
            key = quote(keyname(index))

            if op == "read":
                out.write(
                    "SELECT ycsb_key, field0 FROM usertable WHERE ycsb_key = %s;\n"
                    % key
                )
            elif op == "update":
                out.write(
                    "UPDATE usertable SET field0=%s WHERE ycsb_key = %s;\n"
                    % (quote(fieldvalue(rng, args.field_length)), key)
                )
            elif op == "rmw":
                # YCSB's read-modify-write reads a key then writes it back. A
                # batch SQL file cannot feed the read value into the update, so
                # the write uses a freshly generated value. The access pattern
                # -- same key, read then write -- is preserved; the data
                # dependency is not. Recorded as a deviation.
                out.write(
                    "SELECT ycsb_key, field0 FROM usertable WHERE ycsb_key = %s;\n"
                    % key
                )
                out.write(
                    "UPDATE usertable SET field0=%s WHERE ycsb_key = %s;\n"
                    % (quote(fieldvalue(rng, args.field_length)), key)
                )
            elif op == "scan":
                length = rng.randrange(1, MAX_SCAN_LENGTH + 1)
                out.write(
                    "SELECT ycsb_key FROM usertable WHERE ycsb_key >= %s "
                    "ORDER BY ycsb_key LIMIT %d;\n" % (key, length)
                )

    print("%s %s" % (load_path, run_path))


if __name__ == "__main__":
    main()
