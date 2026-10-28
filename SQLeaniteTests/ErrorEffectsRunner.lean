import SQLeanite.CoreDerivedSQL
import SQLeanite.SQLite.CLI

namespace SQLeanite.Tests
open SQLeanite

private def valueBytes : Core.Value → ByteArray
  | .null => ByteArray.empty
  | .integer value => (toString value.value).toUTF8
  | .realBits bits => (toString (Value.real (Float.ofBits (UInt64.ofNat bits.val)))).toUTF8
  | .text text => ByteArray.mk (SQLite.CLI.listTextBytes text.bytes).toArray
  | .blob blob => ByteArray.mk (SQLite.CLI.listTextBytes blob.bytes).toArray

private def emit (results : List Core.Result) : IO Unit := do
  let stream ← IO.getStdout
  for result in results do
    for row in result.rows do
      let fields := (row.map valueBytes).intersperse "|".toUTF8
      stream.write ((fields.foldl (· ++ ·) ByteArray.empty) ++ "\n".toUTF8)

/-- Test transport for the real state-carrying API. Each complete SQL statement
runs on the preceding outcome state, including after an execution error. -/
def runErrorEffectsScript : IO UInt32 := do
  let stdin ← IO.getStdin
  let bytes ← IO.iterate ByteArray.empty fun bytes => do
    let chunk ← stdin.read 4096
    return if chunk.isEmpty then .inr bytes else .inl (bytes ++ chunk)
  let script := (String.fromUTF8? bytes).getD ""
  let mut state := Core.State.empty
  let mut status := 0
  for source in SQLite.Script.split script do
    match CoreTokenGrammar.parseCertified source with
    | .error message => IO.eprintln s!"Error: {message}"; status := 1
    | .ok parsed =>
        for statement in parsed.statements do
          match CoreDerivedSQL.executeStatementEffects state statement source with
          | .success next results => state := next; emit results
          | .failure next message => state := next; IO.eprintln s!"Error: {message}"; status := 1
  return status

end SQLeanite.Tests
