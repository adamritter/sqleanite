import SQLeanite.SQLite.JsonPretty

namespace SQLeanite.SQLite.JsonExtract
open JsonValid

def nulPrefix (input : Array UInt8) : Array UInt8 :=
  (input.toList.takeWhile (fun c => c != 0)).toArray

def asciiSpace (c : Nat) : Bool := c == 32 || (9 ≤ c && c ≤ 13)

def integerToken (input : Array UInt8) : Int × Int := Id.run do
  let input := nulPrefix input
  if byte input 0 == 48 && [88,120].contains (byte input 1) then
    let start := span input (· == 48) (input.size+1) 2
    let finish := span input hex (input.size+1) start
    let value := (List.range (finish-start)).foldl (fun n i =>
      (n*16 + JsonEscape.hexInt (byte input (start+i))) % (2^64)) 0
    let signed := if value ≥ 2^63 then Int.ofNat value - 2^64 else Int.ofNat value
    return (if finish-start > 16 then 2 else if finish < input.size then 1 else 0, signed)
  let prefixEnd := span input (fun c => digit c || [43,45,32,10,9].contains c) (input.size+1) 0
  let input := input.extract 0 (prefixEnd + if prefixEnd < input.size then 1 else 0)
  let begin := span input asciiSpace (input.size+1) 0
  let negative := byte input begin == 45
  let start := begin + if [43,45].contains (byte input begin) then 1 else 0
  let significant := span input (· == 48) (input.size+1) start
  let finish := span input digit (input.size+1) significant
  let magnitude := (List.range (finish-significant)).foldl (fun n i =>
    min (2^63+1) (n*10 + byte input (significant+i)-48)) 0
  let status := if finish == start then -1
    else if span input asciiSpace (input.size+1) finish == input.size then 0 else 1
  let signed := if negative then -(Int.ofNat (min magnitude (2^63)))
    else Int.ofNat (min magnitude (2^63-1))
  return (if magnitude > 2^63 then 2 else if magnitude == 2^63 && !negative then 3 else status, signed)

def floatToken (input : Array UInt8) : Except String Value := do
  let text := Numeric.numericText (.textBytes input)
  unless (Numeric.parsePrefix text).completeToNul do throw "malformed JSON"
  return .real (Numeric.realPrefix text)

def integerValue (input : Array UInt8) : Except String Value := do
  if input.isEmpty then throw "malformed JSON"
  let negative := byte input 0 == 45
  if negative && input.size < 2 then throw "malformed JSON"
  let inner := if negative then input.extract 1 input.size else input
  let (status, value) := integerToken inner
  if status == 0 then
    if value < 0 then
      let number := Float.ofInt (2^64 + value)
      return .real (if negative then -number else number)
    return .integer (if negative then -value else value)
  if status == 3 && negative then return .integer Numeric.minInt
  if status == 1 then throw "malformed JSON"
  floatToken input

def codepoint (value : Nat) : Array UInt8 :=
  if value ≤ 127 then #[UInt8.ofNat value]
  else if value ≤ 2047 then #[UInt8.ofNat (192+value/64),UInt8.ofNat (128+value%64)]
  else if value < 65536 then #[UInt8.ofNat (224+value/4096),UInt8.ofNat (128+(value/64)%64),UInt8.ofNat (128+value%64)]
  else if value == 629145 then #[]
  else #[UInt8.ofNat (240+value/262144),UInt8.ofNat (128+(value/4096)%64),UInt8.ofNat (128+(value/64)%64),UInt8.ofNat (128+value%64)]

def unescape (input : Array UInt8) : Nat → Nat → Array UInt8 → Array UInt8
  | 0, _, out => out
  | fuel+1, pos, out =>
      if pos ≥ input.size then out
      else if byte input pos == 92 then
        let (value, next) := JsonEscape.unescape input input.size (input.size+1) pos
        unescape input fuel next (out ++ codepoint value)
      else unescape input fuel (pos+1) (out.push (UInt8.ofNat (byte input pos)))

def valueAt (input : Array UInt8) (pos : Nat) : Except String Value := do
  let (header, size) ← JsonAccess.require "malformed JSON" (payload input pos)
  let kind := byte input pos % 16
  let data := input.extract (pos+header) (pos+header+size)
  if kind ≤ 2 then
    unless size == 0 do throw "malformed JSON"
    return if kind == 0 then .null else .integer (if kind == 1 then 1 else 0)
  if kind == 3 || kind == 4 then return ← integerValue data
  if kind == 5 || kind == 6 then return ← floatToken data
  if kind == 7 || kind == 10 then return Text.fromBytes data
  if kind == 8 || kind == 9 then return Text.fromBytes (unescape data (data.size+1) 0 #[])
  if kind == 11 || kind == 12 then return .blob (input.extract pos (pos+header+size))
  throw "malformed JSON"

/-- jsonReturnStringAsBlob deliberately ignores the text parser's status.
Retain its partially built binary on malformed descendants instead of replacing
that behavior with full-document validation. -/
structure PartialEncoding where
  code : Nat
  next : Nat
  data : Array UInt8

def reservedHeader (kind size : Nat) : Array UInt8 :=
  let width := if size < 12 then 0 else if size < 256 then 1 else if size < 65536 then 2 else 4
  let tag := if width == 0 then size else if width == 1 then 12 else if width == 2 then 13 else 14
  #[UInt8.ofNat (tag*16+kind)] ++
    (List.range width).toArray.map (fun i => UInt8.ofNat (size / 256^(width-i-1)))

def uncheckedNumber (input : Array UInt8) (pos : Nat) : Option Parsed := do
  let parsed ← number input pos
  let data := input.extract pos parsed.next
  let special := data.any (fun b => [73,105,88,120].contains b.toNat)
  if !special && [46,69,101].contains (byte input parsed.next) then none else pure parsed

mutual
  def unchecked (input : Array UInt8) : Nat → Nat → Nat → PartialEncoding
    | 0, _, pos => ⟨0,pos,#[]⟩
    | fuel+1, depth, pos => Id.run do
        let pos := (skip input (input.size+1) pos false).1
        let c := byte input pos
        if c == 123 || c == 91 then
          let kind := if c == 123 then 12 else 11
          let header := reservedHeader kind (input.size-pos)
          if depth+1 > 1000 then return ⟨0,pos,header⟩
          return uncheckedMembers input fuel (depth+1) (c == 123) header (pos+1) #[]
        if c == 34 || c == 39 then
          match string input c (input.size+1) (pos+1) (c == 39) with
          | none => return ⟨0,pos,#[]⟩
          | some parsed => return ⟨1,parsed.next,JsonBinary.stringNode input (pos+1) (parsed.next-1)⟩
        if [125,93,44,58].contains c then
          return ⟨if c == 125 then 2 else if c == 93 then 3 else if c == 44 then 4 else 5,pos,#[]⟩
        let parsed := if digit c || [43,45,46].contains c then uncheckedNumber input pos else atom input pos
        match parsed with
        | none => return ⟨0,pos,#[]⟩
        | some parsed => return ⟨1,parsed.next,JsonBinary.numberNode (input.extract pos parsed.next)⟩
  def uncheckedMembers (input : Array UInt8) : Nat → Nat → Bool → Array UInt8 → Nat → Array UInt8 → PartialEncoding
    | 0, _, _, header, pos, out => ⟨0,pos,header ++ out⟩
    | fuel+1, depth, object, header, pos, out => Id.run do
        let close := if object then 2 else 3
        let mut item := unchecked input fuel depth pos
        if item.code == close then return ⟨1,item.next+1,JsonAccess.node (if object then 12 else 11) out⟩
        let mut out := out
        if object then
          if item.code != 1 then
            let begin := (skip input (input.size+1) pos false).1
            match identifier input begin with
            | none => return ⟨0,item.next,header ++ out ++ item.data⟩
            | some label => item := ⟨1,label.next,item.data ++ JsonBinary.stringNode input begin label.next⟩
          out := out ++ item.data
          let kind := byte item.data 0 % 16
          if kind < 7 || kind > 10 then return ⟨0,pos,header ++ out⟩
          let mut next := item.next
          if byte input next != 58 then
            next := span input (fun c => [9,10,13,32].contains c) (input.size+1) next
          if byte input next == 58 then next := next+1
          else
            let colon := unchecked input fuel depth next
            out := out ++ colon.data
            if colon.code != 5 then return ⟨0,next,header ++ out⟩
            next := colon.next+1
          item := unchecked input fuel depth next
        out := out ++ item.data
        if item.code != 1 then return ⟨0,item.next,header ++ out⟩
        let mut next := item.next
        if byte input next != 44 && byte input next != (if object then 125 else 93) then
          next := span input (fun c => [9,10,13,32].contains c) (input.size+1) next
        if byte input next == 44 then
          return uncheckedMembers input fuel depth object header (next+1) out
        if byte input next == (if object then 125 else 93) then
          return ⟨1,next+1,JsonAccess.node (if object then 12 else 11) out⟩
        let separator := unchecked input fuel depth next
        out := out ++ separator.data
        if separator.code == 4 then return uncheckedMembers input fuel depth object header (separator.next+1) out
        if separator.code == close then return ⟨1,separator.next+1,JsonAccess.node (if object then 12 else 11) out⟩
        return ⟨0,next,header ++ out⟩
end

def evaluate (arguments : List Value) : Except String Value := do
  let value :: paths := arguments | return .null
  if paths.isEmpty then return .null
  let encoded ← JsonBinary.evaluate value
  let .blob input := encoded | return .null
  if let [path] := paths then
    let some pos ← JsonAccess.select input (some path) | return .null
    return ← valueAt input pos
  let mut chunks := [#[91]]
  let mut first := true
  -- Malformed rendering is deferred until jsonReturnString. Later path
  -- failures supersede it, and a NULL path discards it. Depth errors have
  -- already reached the SQL context and survive a later NULL path.
  let mut renderingError : Option String := none
  for path in paths do
    if Text.isNull path then
      if renderingError == some "JSON nested too deep" then throw "JSON nested too deep"
      return .null
    if first then first := false else chunks := chunks ++ [#[44]]
    let pos ← JsonAccess.select input (some path)
    match pos with
    | none => chunks := chunks ++ ["null".toUTF8.data]
    | some pos =>
        if renderingError.isNone then
          match JsonPretty.render input #[] (4*input.size+4) false 0 0 pos with
          | .ok rendered => chunks := chunks ++ rendered.chunks
          | .error message => renderingError := some message
  if let some message := renderingError then throw message
  chunks := chunks ++ [#[93]]
  let text := chunks.foldl (fun out chunk => out ++ chunk) #[]
  return .blob (unchecked text (4*text.size+4) 0 0).data


theorem evaluate_no_arguments : evaluate [] = .ok .null := rfl

theorem evaluate_one_argument (value : Value) : evaluate [value] = .ok .null := rfl

theorem integerValue_empty : integerValue #[] = .error "malformed JSON" := rfl

theorem valueAt_truncated (input : Array UInt8) (pos : Nat)
    (truncated : payload input pos = none) :
    valueAt input pos = .error "malformed JSON" := by
  simp only [valueAt, truncated, JsonAccess.require] <;> rfl

end SQLeanite.SQLite.JsonExtract
