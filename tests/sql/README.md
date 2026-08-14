# SQLeanite focused upstream tests

`runner.tcl` loads an unmodified upstream SQLite Tcl test file with the
SQLeanite compatibility shim in this directory. Run focused files from a
temporary working directory so generated `test.db` connection labels do not
touch files in the checkout:

```sh
scripts/run-focused-upstream.sh select1 insert
```

With no arguments, the script runs those two bounded samples. On 2026-08-11:

- `select1.test`: 191 tests, 0 failures;
- `insert.test`: 76 tests, 0 failures.

These 267 assertions are a focused sample, not the full upstream suite. The
full suite is intentionally run infrequently because it is much more expensive
against the Lean implementation.

The restricted persisted route has its own deterministic comparison corpus:

```sh
scripts/run-mvp-differential-smoke.sh
```

It compares seven SQL files byte-for-byte against C SQLite using separate real
database files for each implementation.
