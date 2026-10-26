import SQLeanite.SQLite.JsonAccess

namespace SQLeanite.SQLite.JsonBinary
open JsonValid

/-- Storage opcodes retain canonical versus JSON5 escapes without decoding
or re-encoding the payload bytes. Input validity is checked before encoding. -/
def stringKind (input : Array UInt8) : Nat → Nat → Nat → Nat
  | 0, _, kind => kind
  | fuel+1, pos, kind =>
      if pos ≥ input.size then kind else
      let c := byte input pos
      if c == 92 then
        let escape := byte input (pos+1)
        let canonical := [34,92,47,98,102,110,114,116,117].contains escape
        stringKind input fuel (pos+2) (if canonical then if kind == 7 then 8 else kind else 9)
      else stringKind input fuel (pos+1) (if c ≤ 31 || c == 34 then 9 else kind)

def stringNode (input : Array UInt8) (start finish : Nat) : Array UInt8 :=
  let data := input.extract start finish
  JsonAccess.node (stringKind data (data.size+1) 0 7) data

def numberNode (input : Array UInt8) : Array UInt8 := Id.run do
  let name := input.toList.map (fun b => lower b.toNat)
  if name == [116,114,117,101] then return JsonAccess.node 1 #[]
  if name == [102,97,108,115,101] then return JsonAccess.node 2 #[]
  if name == [110,117,108,108] || name.contains 110 && !name.contains 105 then
    return JsonAccess.node 0 #[]
  if name.contains 105 then
    return JsonAccess.node 5 (if byte input 0 == 45 then "-9e999".toUTF8.data else "9e999".toUTF8.data)
  let data := if byte input 0 == 43 then input.extract 1 input.size else input
  let hex := name.contains 120
  let floating := name.contains 46 || name.contains 101
  let first := if byte data 0 == 45 then 1 else 0
  let extended := byte data first == 46 || byte data (data.size-1) == 46 ||
    (List.range data.size).any (fun i => byte data i == 46 && [69,101].contains (byte data (i+1)))
  return JsonAccess.node (if hex then 4 else if floating then if extended then 6 else 5 else 3) data

mutual
  def encode (input : Array UInt8) : Nat → Nat → Option JsonAccess.Encoded
    | 0, _ => none
    | fuel+1, pos => do
        let pos := (skip input (input.size+1) pos false).1
        let c := byte input pos
        if c == 123 || c == 91 then
          let children ← members input fuel (c == 123) (pos+1) #[]
          return { children with data := JsonAccess.node (if c == 123 then 12 else 11) children.data }
        if c == 34 || c == 39 then
          let parsed ← string input c (input.size+1) (pos+1) (c == 39)
          return ⟨parsed.next, stringNode input (pos+1) (parsed.next-1)⟩
        let parsed ← if digit c || [43,45,46].contains c then number input pos else atom input pos
        return ⟨parsed.next, numberNode (input.extract pos parsed.next)⟩
  def members (input : Array UInt8) : Nat → Bool → Nat → Array UInt8 → Option JsonAccess.Encoded
    | 0, _, _, _ => none
    | fuel+1, object, pos, collected => do
        let pos := (skip input (input.size+1) pos false).1
        let close := if object then 125 else 93
        if byte input pos == close then return ⟨pos+1, collected⟩
        let (pos, collected) ← if object then do
            let c := byte input pos
            let (finish, data) ← if c == 34 || c == 39 then do
                let parsed ← string input c (input.size+1) (pos+1) (c == 39)
                pure (parsed.next, stringNode input (pos+1) (parsed.next-1))
              else do
                let parsed ← identifier input pos
                pure (parsed.next, stringNode input pos parsed.next)
            let colon := (skip input (input.size+1) finish false).1
            unless byte input colon == 58 do none
            pure (colon+1, collected ++ data)
          else pure (pos, collected)
        let child ← encode input fuel pos
        let after := (skip input (input.size+1) child.next false).1
        let collected := collected ++ child.data
        if byte input after == close then return ⟨after+1, collected⟩
        unless byte input after == 44 do none
        members input fuel object (after+1) collected
end

def evaluate (value : Value) : Except String Value := do
  if Text.isNull value then return .null
  let input := Text.bytes value
  if (match value with | .blob _ => blobLooks input | _ => false) then return .blob input
  unless textValid input true do throw "malformed JSON"
  let some parsed := encode input (4*input.size+4) 0 | throw "malformed JSON"
  return .blob parsed.data


theorem evaluate_null : evaluate .null = .ok .null := rfl

theorem evaluate_admitted_blob (input : Array UInt8) (admitted : blobLooks input = true) :
    evaluate (.blob input) = .ok (.blob input) := by
  simp [evaluate, Text.isNull, Text.bytes, admitted, pure, Except.pure]

theorem evaluate_invalid_text (input : Array UInt8) (invalid : textValid input true = false) :
    evaluate (.textBytes input) = .error "malformed JSON" := by
  simp only [evaluate, Text.isNull, Text.bytes, invalid] <;> rfl

theorem stringKind_empty (fuel pos kind : Nat) : stringKind #[] fuel pos kind = kind := by
  cases fuel <;> simp [stringKind]

end SQLeanite.SQLite.JsonBinary
