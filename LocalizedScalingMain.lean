import SQLeanite.CoreRuntime

open SQLeanite

/-- Time only one localized commit on an already-open connection. Database
decode and proof-state reconstruction happen before the clock starts. -/
def main (args : List String) : IO UInt32 := do
  let (databasePath, sql) ← match args with
    | [databasePath, "--sql-file", sqlFile] =>
        pure (databasePath, ← IO.FS.readFile sqlFile)
    | [databasePath, rowid, marker] =>
        pure (databasePath,
          s!"UPDATE t SET payload='localized-{marker}' WHERE id={rowid};")
    | _ => do
        IO.eprintln "usage: localized_scaling DB ROWID MARKER | DB --sql-file SQL-FILE"
        return 2
  let paths : CoreFileAdapter.Paths := {
    main := databasePath, journal := databasePath ++ "-journal" }
  let connection ← CoreFileEngine.reopen .system paths
  let started ← IO.monoMsNow
  let outcome ← CoreFileEngine.execute connection sql
  let finished ← IO.monoMsNow
  match outcome with
  | .error message =>
      IO.eprintln message
      return 1
  | .ok _ =>
      IO.println (finished - started)
      return 0
