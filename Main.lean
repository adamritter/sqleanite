import SQLeanite.SQLite.CLI
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

/-- The pinned CLI preserves non-control bytes, stops at NUL, and escapes
C0 controls in list mode. Formatting remains separate from SQL values. -/
private def coreValueBytes : PhysicalCodec.Value → ByteArray
  | .null => ByteArray.empty
  | .integer value => (toString value.value).toUTF8
  | .realBits bits => (toString (SQLeanite.Value.real
      (Float.ofBits (UInt64.ofNat bits.val)))).toUTF8
  | .text text => ByteArray.mk (SQLite.CLI.listTextBytes text.bytes).toArray
  | .blob blob => ByteArray.mk (SQLite.CLI.listTextBytes blob.bytes).toArray

private def renderCoreResult (result : Core.Result) : ByteArray :=
  result.rows.foldl (fun output row =>
    let fields := (row.map coreValueBytes).intersperse "|".toUTF8
    (fields.foldl (· ++ ·) output) ++ "\n".toUTF8) ByteArray.empty

private def printCoreResults (results : List Core.Result) : IO Unit := do
  let stream ← IO.getStdout
  for result in results do
    let bytes := renderCoreResult result
    unless bytes.isEmpty do stream.write bytes

/-- Retain original statement text and its write classification without keeping
the complete parser AST alive while a large script executes. -/
private structure PreparedStatement where
  sql : String
  writes : Bool

/-- Every complete source statement uses the certified grammar. A malformed
statement is conservatively classified as a potential write for preflight. -/
private def statementMightWrite (sql : String) : Bool :=
  match CoreTokenGrammar.parseStatements sql with
  | .ok statements => statements.toList.any CoreFileEngine.statementWrites
  | .error _ => true

private def prepareScript (sql : String) : Array PreparedStatement :=
  (SQLite.Script.split sql).toArray.map fun source => {
    sql := source, writes := statementMightWrite source }

/-- Fail before logical execution when a mutating batch targets a file the OS
will not open read/write.  Besides producing the SQLite-style diagnostic, this
prevents an earlier semantic error in a multi-statement batch from masking the
more fundamental read-only condition.  Opening in `readWrite` does not truncate
or otherwise modify the file. -/
private def requireWritableFor (path : System.FilePath) (sql : String)
    (prepared : Option (Array PreparedStatement) := none) : IO Unit := do
  let writes := match prepared with
    | some lines => lines.any (fun line => line.writes)
    | none => (prepareScript sql).any (·.writes)
  if writes && (← path.pathExists) then
    try
      IO.FS.withFile path .readWrite fun _ => pure ()
    catch _ =>
      throw (IO.userError "attempt to write a readonly database")

/-- Execute preflighted source statements, discarding each parsed AST before
the next statement. Results are accumulated in execution order. -/
private def executePreparedStatements (connection : CoreFileEngine.Connection)
    (lines : Array PreparedStatement) : IO (Except String (List Core.Result)) := do
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
    let prepared := prepareScript sql
    if fileExists then requireWritableFor mainPath sql (some prepared)
    -- The page-local insert. `CoreLazyWrite.insertPlan_refines` proves it denotes
    -- the ordered insert, but only under `WellFormedTree`, and nothing checks
    -- those premises at open time yet. So it stays behind an explicit opt-in
    -- rather than defaulting on: the shipped path must not rest on an unchecked
    -- structural assumption. Set SQLEANITE_PAGE_LOCAL_WRITES=1 to measure it.
    let pageLocalEnabled := (← IO.getEnv "SQLEANITE_PAGE_LOCAL_WRITES") == some "1"
    let lazyWrite ← if fileExists && pageLocalEnabled then
        match CoreTokenGrammar.parseStatements sql with
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
      printCoreResults [result]
      return 0
    let outcome ← if fileExists then do
      match ← CoreLazyFileEngine.execute? paths sql with
      | some result => pure result
      | none => do
          let connection ← CoreFileEngine.reopen .system paths
          executePreparedStatements connection prepared
    else do
      let connection ← CoreFileEngine.create .system paths
      executePreparedStatements connection prepared
    match outcome with
    | .error message =>
        IO.eprintln s!"Error: {message}"
        pure 1
    | .ok results =>
        printCoreResults results
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
  let statements := (SQLite.Script.split sql).flatMap fun source =>
    ((CoreTokenGrammar.parseStatements source).toOption.getD #[]).toList
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
      printCoreResults results
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
    let statements := (sql.splitOn "\n").filter fun line => !line.trimAscii.toString.isEmpty
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
          printCoreResults results
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
