import SQLeanite.CoreLazyWrite
import SQLeanite.CoreRuntime

open SQLeanite

/- The executable is deliberately a thin shell over `CoreRuntime`; verified
runtime substitutions (including stack-safe page-delta construction) remain
owned by the imported core modules. -/

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

/-- A preflighted line from a script whose physical lines are independently
parseable statements.  Keeping only the source and write bit lets large load
files discard each statement AST before parsing the next one. -/
private structure PreparedLine where
  sql : String
  writes : Bool

private inductive LineQuote where
  | none
  | single
  | double
deriving BEq

/-- A physical line is a safe script boundary only when it ends in a
semicolon outside any SQL string or quoted identifier.  Toggling on each quote
also handles SQL's doubled-quote escape: the two adjacent toggles cancel. -/
private def standaloneSQLLine (line : String) : Bool :=
  let finalQuote := line.foldl (init := LineQuote.none) fun quote char =>
    match quote, char with
    | .none, '\'' => .single
    | .none, '"' => .double
    | .single, '\'' => .none
    | .double, '"' => .none
    | current, _ => current
  finalQuote == .none && line.trim.endsWith ";"

/-- Conservative write classification for the read-only-file diagnostic.
Ambiguous statements are treated as writes; actual statement classification
inside the engine still comes from the parsed `Statement`. -/
private def lineMightWrite (line : String) : Bool :=
  let normalized := line.trim.toUpper
  !(normalized.startsWith "SELECT" || normalized.startsWith "PRAGMA" ||
    normalized.startsWith "EXPLAIN")

/-- Recognize the line-oriented format emitted by the benchmark and import
tools.  This is only an execution-space optimization: every nonempty line must
end at an unquoted semicolon, and the ordinary parser still processes that
line before execution.  Any multiline or otherwise general SQL script returns
`none` and follows the original whole-script path. -/
private def prepareLineScript? (sql : String) : Option (Array PreparedLine) :=
  let lines := (sql.splitOn "\n").filter fun line => !line.trim.isEmpty
  if lines.all standaloneSQLLine then
    some <| lines.toArray.map fun line => {
      sql := line
      writes := lineMightWrite line }
  else none

/-- Fail before logical execution when a mutating batch targets a file the OS
will not open read/write.  Besides producing the SQLite-style diagnostic, this
prevents an earlier semantic error in a multi-statement batch from masking the
more fundamental read-only condition.  Opening in `readWrite` does not truncate
or otherwise modify the file. -/
private def requireWritableFor (path : System.FilePath) (sql : String)
    (prepared : Option (Array PreparedLine) := none) : IO Unit := do
  let writes := match prepared with
    | some lines => lines.any (fun line => line.writes)
    | none => match parse sql with
      | .ok statements => statements.toList.any CoreFileEngine.statementWrites
      | .error _ => false
  if writes && (← path.pathExists) then
    try
      IO.FS.withFile path .readWrite fun _ => pure ()
    catch _ =>
      throw (IO.userError "attempt to write a readonly database")

/-- Execute a preflighted line script while retaining neither the complete
parser AST nor completed statement results.  Results are accumulated in the
same order as `CoreFileEngine.execute`; load statements ordinarily contribute
empty results, so this remains constant-space in the number of loaded rows. -/
private def executePreparedLines (connection : CoreFileEngine.Connection)
    (lines : Array PreparedLine) : IO (Except String (List Core.Result)) := do
  let mut reversed : List Core.Result := []
  for line in lines do
    match ← CoreFileEngine.execute connection line.sql with
    | .error message => return .error message
    | .ok results =>
        reversed := results.foldl (fun acc result => result :: acc) reversed
  return .ok reversed.reverse

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
    let prepared := prepareLineScript? sql
    if fileExists then requireWritableFor mainPath sql prepared
    -- SPIKE, unproved: try the page-local insert first so its cost can be
    -- measured. Must not survive into a shipped build until the refinement in
    -- docs/LAZY_WRITE_DESIGN.md is discharged.
    let lazyWrite ← if fileExists then
        match parse sql with
        | .ok parsed =>
            match parsed.toList with
            | [.insert table columns rows] =>
                match rows.toList with
                | [expressions] =>
                    CoreLazyWrite.executeInsert? .system paths
                      (CoreSQL.canonical table) columns expressions
                | _ => pure none
            | _ => pure none
        | .error _ => pure none
      else pure none
    if let some result := lazyWrite then
      let text := renderCoreResult result
      unless text.isEmpty do IO.println text
      return 0
    let outcome ← if fileExists then do
      match ← CoreLazyFileEngine.execute? paths sql with
      | some result => pure result
      | none => do
          let connection ← CoreFileEngine.reopen .system paths
          match prepared with
          | some lines => executePreparedLines connection lines
          | none => CoreFileEngine.execute connection sql
    else do
      let connection ← CoreFileEngine.create .system paths
      match prepared with
      | some lines => executePreparedLines connection lines
      | none => CoreFileEngine.execute connection sql
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

/-- Execute one statement per input line on a single connection, reporting each
statement's wall-clock microseconds on stderr as `time<TAB>micros`.

Exists so latency percentiles can be measured at all. The ordinary batch mode
executes a whole script under one `execute` call, so timing it externally
measures the open plus the script, and timing one statement per process measures
process startup and a fresh open -- at 32 ms/MB the open dominates and any
per-operation number derived that way is meaningless. Holding one connection and
timing each statement separately is the only honest way to get a distribution.

Input is split on newlines, so it suits generated one-statement-per-line traces
such as `scripts/ycsb-trace.py` output. It is a measurement aid, not a general
SQL splitter: a statement spanning lines will be rejected by the parser. -/
private def coreBatchTimed (databasePath : String) (args : List String) :
    IO UInt32 := do
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
    let connection ← if fileExists then CoreFileEngine.reopen .system paths
      else CoreFileEngine.create .system paths
    let statements := (sql.splitOn "\n").filter fun line => !line.trim.isEmpty
    let mut status : UInt32 := 0
    for statement in statements do
      let started ← IO.monoNanosNow
      let outcome ← CoreFileEngine.execute connection statement
      let ended ← IO.monoNanosNow
      IO.eprintln s!"time\t{(ended - started) / 1000}"
      match outcome with
      | .error message =>
          IO.eprintln s!"Error: {message}"
          status := 1
      | .ok results =>
          let text := String.intercalate "\n" <|
            (results.map renderCoreResult).filter fun output => !output.isEmpty
          unless text.isEmpty do IO.println text
    pure status

private def runMain (args : List String) : IO UInt32 :=
  match args with
  | "--verified-file" :: databasePath :: rest => coreBatch databasePath rest
  | "--verified-file-timed" :: databasePath :: rest =>
      coreBatchTimed databasePath rest
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
