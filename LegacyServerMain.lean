import SQLeanite.Engine

open SQLeanite

/-!
The upstream Tcl compatibility transport. This executable deliberately drives
the broad, unverified in-memory interpreter and is not the shipped `sqleanite`
binary. Keeping the protocol in its own root prevents conformance coverage from
silently widening the production trust claim.
-/

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + n - 10)

private def hexEncode (s : String) : String :=
  String.mk <| s.toUTF8.toList.flatMap fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

private def nibble? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def decodeBytes (chars : List Char)
    (output : ByteArray := ByteArray.empty) : Option ByteArray :=
  match chars with
  | [] => some output
  | first :: second :: rest => do
      let high ← nibble? first
      let low ← nibble? second
      decodeBytes rest (output.push (UInt8.ofNat (high * 16 + low)))
  | _ => none

private def hexDecode? (s : String) : Option String := do
  String.fromUTF8? (← decodeBytes s.toList)

private def flattenValues (result : QueryResult) : Array Value :=
  result.rows.foldl (init := #[]) fun output row => output ++ row

private def send (line : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn line
  stdout.flush

private def serverLoop (database : Database) : IO UInt32 :=
  IO.iterate database fun state => do
    let stdin ← IO.getStdin
    let line ← stdin.getLine
    if line.isEmpty then return .inr 0
    match hexDecode? line.trimAscii.toString with
    | none =>
        send s!"ERR\t{hexEncode "invalid hex request"}"
        return .inl state
    | some sql =>
        let (next, outcome) := runSQLProgress state sql
        match outcome with
        | .error message =>
            send s!"ERR\t{hexEncode message}"
            return .inl next
        | .ok result =>
            let values := flattenValues result
            let names := result.columns.toList.map hexEncode
            let encodedValues := values.toList.map fun value =>
              hexEncode value.clientText
            let nulls := values.toList.map fun value =>
              if value matches .null then "1" else "0"
            send s!"OK\t{values.size}\t{result.columns.size}\t{String.intercalate "," names}\t{String.intercalate "," encodedValues}\t{result.changes}\t{if result.reportsChanges then 1 else 0}\t{String.intercalate "," nulls}"
            return .inl next

def main (args : List String) : IO UInt32 :=
  match args with
  | [] | ["--server"] => serverLoop {}
  | _ => do
      IO.eprintln "usage: sqleanite_legacy_server [--server]"
      pure 1
