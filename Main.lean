import SQLeanite.CoreRuntime

open SQLeanite

/-- Read a stream to EOF under an explicit chunk budget.

Written with `IO.iterate` rather than `partial def` so the project keeps zero
local partial definitions; `IO.iterate` is itself an opaque runtime primitive
and is accounted for in `docs/TRUST.md` as part of the executable I/O boundary. -/
private def readStreamToEnd (stream : IO.FS.Stream) : IO String := do
  let acc ← IO.iterate ByteArray.empty fun acc => do
    let chunk ← stream.read 4096
    if chunk.isEmpty then return .inr acc else return .inl (acc ++ chunk)
  return String.fromUTF8? acc |>.getD ""

private def coreValueText : PhysicalCodec.Value → String
  | .null => ""
  | .integer value => toString value.value
  | .realBits bits => toString (SQLeanite.Value.real
      (Float.ofBits (UInt64.ofNat bits.val)))
  | .text text => String.fromUTF8? (ByteArray.mk text.bytes.toArray) |>.getD ""
  | .blob blob =>
      (SQLeanite.Value.blob blob.bytes.toArray).clientText

private def renderCoreResult (result : Core.Result) : String :=
  String.intercalate "\n" <| result.rows.map fun row =>
    String.intercalate "|" (row.map coreValueText)

/-- Fail before logical execution when a mutating batch targets a file the OS
will not open read/write.  Besides producing the SQLite-style diagnostic, this
prevents an earlier semantic error in a multi-statement batch from masking the
more fundamental read-only condition.  Opening in `readWrite` does not truncate
or otherwise modify the file. -/
private def requireWritableFor (path : System.FilePath) (sql : String) : IO Unit := do
  let writes := match parse sql with
    | .ok statements => statements.toList.any CoreFileEngine.statementWrites
    | .error _ => false
  if writes && (← path.pathExists) then
    try
      IO.FS.withFile path .readWrite fun _ => pure ()
    catch _ =>
      throw (IO.userError "attempt to write a readonly database")

private def coreBatch (databasePath : String) (args : List String) : IO UInt32 := do
  let sql ←
    match args with
    | file :: _ => IO.FS.readFile file
    | [] => readStreamToEnd (← IO.getStdin)
  let mainPath : System.FilePath := databasePath
  let paths : CoreFileAdapter.Paths := {
    main := mainPath, journal := databasePath ++ "-journal" }
  let process := (← IO.Process.getPID).toNat
  let lock : ProcessLock.Config := {
    directory := databasePath ++ ".sqleanite-lock", process }
  ProcessLock.withLock lock do
    let fileExists ← mainPath.pathExists
    requireWritableFor mainPath sql
    let outcome ← if fileExists then do
      match ← CoreLazyFileEngine.execute? paths sql with
      | some result => pure result
      | none => do
          let connection ← CoreFileEngine.reopen .system paths
          CoreFileEngine.execute connection sql
    else do
      let connection ← CoreFileEngine.create .system paths
      CoreFileEngine.execute connection sql
    match outcome with
    | .error message =>
        IO.eprintln s!"Error: {message}"
        pure 1
    | .ok results =>
        let text := String.intercalate "\n" <|
          (results.map renderCoreResult).filter fun output => !output.isEmpty
        unless text.isEmpty do IO.println text
        pure 0

private def coreWALBatch (databasePath : String) (args : List String) : IO UInt32 := do
  let sql ←
    match args with
    | file :: _ => IO.FS.readFile file
    | [] => readStreamToEnd (← IO.getStdin)
  let paths : CoreWALFileAdapter.Paths := {
    main := databasePath, wal := databasePath ++ "-wal" }
  let process := (← IO.Process.getPID).toNat
  let lock : ProcessLock.Config := {
    directory := databasePath ++ ".sqleanite-lock", process }
  let statements := match parse sql with
    | .ok parsed => parsed.toList
    | .error _ => []
  let run : IO (Except String (List Core.Result)) := do
    requireWritableFor databasePath sql
    unless ← (databasePath : System.FilePath).pathExists do
      CoreWALFileAdapter.create .system paths Core.Database.empty
    CoreWALFileEngine.execute .system paths sql
  -- Readers never publish, so only writers take the cross-process lock.
  let outcome ← if CoreWALFileEngine.needsWriter statements then
      ProcessLock.withLock lock run
    else run
  match outcome with
  | .error message =>
      IO.eprintln s!"Error: {message}"
      pure 1
  | .ok results =>
      let text := String.intercalate "\n" <|
        (results.map renderCoreResult).filter fun output => !output.isEmpty
      unless text.isEmpty do IO.println text
      pure 0

private def coreWALCheckpoint (databasePath : String) : IO UInt32 := do
  let paths : CoreWALFileAdapter.Paths := {
    main := databasePath, wal := databasePath ++ "-wal" }
  let process := (← IO.Process.getPID).toNat
  let lock : ProcessLock.Config := {
    directory := databasePath ++ ".sqleanite-lock", process }
  ProcessLock.withLock lock (CoreWALFileEngine.checkpoint .system paths)
  pure 0

private def runMain (args : List String) : IO UInt32 :=
  match args with
  | "--verified-file" :: databasePath :: rest => coreBatch databasePath rest
  | "--verified-wal-file" :: databasePath :: rest => coreWALBatch databasePath rest
  | "--verified-wal-checkpoint" :: databasePath :: _ => coreWALCheckpoint databasePath
  | "--help" :: _ => do
    IO.println "usage: sqleanite [--verified-file DB [SQL-FILE] | --verified-wal-file DB [SQL-FILE] | --verified-wal-checkpoint DB]"
    pure 0
  | _ => do
    IO.eprintln "usage: sqleanite --verified-file DB [SQL-FILE] | --verified-wal-file DB [SQL-FILE] | --verified-wal-checkpoint DB"
    pure 1

/-- Convert host-I/O failures into ordinary CLI diagnostics.  Leaving them
uncaught makes deliberate rejection of corrupt or read-only input look like a
process crash even though the engine has failed safely. -/
def main (args : List String) : IO UInt32 := do
  try runMain args
  catch error =>
    IO.eprintln s!"Error: {error}"
    pure 1
