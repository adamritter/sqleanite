import SQLeanite.SQLite.JsonExtract

namespace SQLeanite.SQLite.JsonRemove
open JsonValid

structure Ancestor where
  pos : Nat
  header : Nat
  size : Nat

structure Location where
  label : Nat
  ancestors : List Ancestor

mutual
  def locate (input : Array UInt8) (target : Nat) : Nat → Nat → Nat → Except String Location
    | 0, _, _ => .error "malformed JSON"
    | fuel+1, root, label => do
        if root == target then return ⟨label, []⟩
        let (header, size) ← JsonAccess.require "malformed JSON" (payload input root)
        let kind := byte input root % 16
        unless kind == 11 || kind == 12 do throw "malformed JSON"
        let found ← locateMembers input target fuel (kind == 12) (root+header) (root+header+size)
        return { found with ancestors := found.ancestors ++ [⟨root,header,size⟩] }
  def locateMembers (input : Array UInt8) (target : Nat) : Nat → Bool → Nat → Nat → Except String Location
    | 0, _, _, _ => .error "malformed JSON"
    | fuel+1, object, pos, finish => do
        if pos ≥ finish then throw "malformed JSON"
        let (value, label) ← if object then do
            let (header, size) ← JsonAccess.require "malformed JSON" (payload input pos)
            pure (pos+header+size, pos)
          else pure (pos,0)
        if value == target then return ⟨label, []⟩
        let (header, size) ← JsonAccess.require "malformed JSON" (payload input value)
        let next := value+header+size
        if value < target && target < next then return ← locate input target fuel value label
        locateMembers input target fuel object next finish
end

/-- Remove the selected value (and its object label), then update only its
ancestor headers. Changed headers use the minimum width, while untouched
binary slices retain their original bytes and header widths. -/
def erase (input : Array UInt8) (pos : Nat) : Except String (Array UInt8) := do
  let location ← locate input pos (4*input.size+4) 0 0
  let (header, size) := (payload input pos).getD (0,0)
  let begin := if location.label > 0 then location.label else pos
  let count := header+size+(pos-begin)
  let mut bytes := input.extract 0 begin ++ input.extract (begin+count) input.size
  let mut delta := -(Int.ofNat count)
  for ancestor in location.ancestors do
    if delta != 0 then
      let size := ((Int.ofNat ancestor.size + delta) % (2^32)).toNat
      let replacement := JsonExtract.reservedHeader (byte input ancestor.pos % 16) size
      bytes := bytes.extract 0 ancestor.pos ++ replacement ++
        bytes.extract (ancestor.pos+ancestor.header) bytes.size
      delta := delta + Int.ofNat replacement.size - Int.ofNat ancestor.header
  return bytes

def evaluate (arguments : List Value) : Except String Value := do
  let value :: paths := arguments | return .null
  let encoded ← JsonBinary.evaluate value
  let .blob input := encoded | return .null
  let mut input := input
  for pathValue in paths do
    if Text.isNull pathValue then return .null
    let path := Text.bytes pathValue
    unless byte path 0 == 36 do throw (JsonAccess.pathError path)
    if byte path 1 == 0 then return .null
    let pos ← JsonAccess.select input (some pathValue)
    if let some pos := pos then input := ← erase input pos
  return .blob input


theorem evaluate_no_arguments : evaluate [] = .ok .null := rfl

theorem evaluate_null (paths : List Value) : evaluate (.null :: paths) = .ok .null := rfl

theorem evaluate_identity (input : Array UInt8) (admitted : blobLooks input = true) :
    evaluate [.blob input] = .ok (.blob input) := by
  simp only [evaluate, JsonBinary.evaluate_admitted_blob input admitted] <;> rfl

theorem locate_target (input : Array UInt8) (target label fuel : Nat) :
    locate input target (fuel+1) target label = .ok ⟨label, []⟩ := by
  simp [locate, pure, Except.pure]

end SQLeanite.SQLite.JsonRemove
