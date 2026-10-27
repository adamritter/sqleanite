import SQLeanite.SQLite.JsonText

namespace SQLeanite.SQLite.JsonTable
open JsonValid

structure Entry where
  id : Nat
  pos : Nat
  key : Value := .null
  fullkey : Array UInt8
  path : Array UInt8
  parent : Option Nat := none

def bounds (input : Array UInt8) (pos : Nat) : Except String (Nat × Nat) := do
  let (header,size) ← JsonAccess.require "malformed JSON" (payload input pos)
  unless pos + header + size ≤ input.size do throw "malformed JSON"
  return (header,size)

def alpha (c : UInt8) : Bool :=
  (65 ≤ c.toNat && c.toNat ≤ 90) || (97 ≤ c.toNat && c.toNat ≤ 122)

def objectSegment (label : Array UInt8) : Array UInt8 :=
  let quote := !(label[0]?.any alpha) ||
    !label.all (fun c => alpha c || (48 ≤ c.toNat && c.toNat ≤ 57))
  let label := (label.toList.takeWhile (· != 0)).toArray
  if quote then ".\"".toUTF8.data ++ label ++ #[34] else #[46] ++ label

def childrenLoop (input : Array UInt8) (finish : Nat) (object : Bool)
    (parent : Entry) : Nat → Nat → Nat → Except String (List Entry)
  | 0, _, _ => .error "malformed JSON"
  | fuel+1, pos, index => do
      if pos == finish then return []
      if pos > finish then throw "malformed JSON"
      let (valuePos,key,segment) ← if object then do
          let kind := byte input pos % 16
          unless 7 ≤ kind && kind ≤ 10 do throw "malformed JSON"
          let (header,size) ← bounds input pos
          let key ← JsonExtract.valueAt input pos
          pure (pos+header+size,key,objectSegment (input.extract (pos+header) (pos+header+size)))
        else pure (pos,Value.integer index,s!"[{index}]".toUTF8.data)
      let (header,size) ← bounds input valuePos
      let next := valuePos+header+size
      unless next ≤ finish do throw "malformed JSON"
      let child : Entry := {
        id := pos
        pos := valuePos
        key := key
        fullkey := parent.fullkey ++ segment
        path := parent.fullkey
        parent := some parent.id }
      return child :: (← childrenLoop input finish object parent fuel next (index+1))

def children (input : Array UInt8) (parent : Entry) : Except String (List Entry) := do
  let kind := byte input parent.pos % 16
  unless kind == 11 || kind == 12 do return []
  let (header,size) ← bounds input parent.pos
  childrenLoop input (parent.pos+header+size) (kind == 12) parent (input.size+1) (parent.pos+header) 0

/-- Object member IDs refer to their label header, not the value header. -/
def findEntry (input : Array UInt8) (selected : Nat) : Nat → List Entry → Except String Entry
  | 0, _ => .error "malformed JSON"
  | _+1, [] => .error "malformed JSON"
  | fuel+1, entry :: rest => do
      if entry.pos == selected then return entry
      findEntry input selected fuel ((← children input entry) ++ rest)

/-- Port jsonEachPathLength's root-row rule, including non-first selected
members where a textual parent baseLength is not a header-adjacent ancestor. -/
def rootPathLength (input path : Array UInt8) (id : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | fuel+1, n =>
      if n ≤ 1 then 1 else
      let n := n-1
      if byte path n == 91 || byte path n == 46 then
        match JsonAccess.select input (some (Text.fromBytes (path.extract 0 n))) with
        | .ok (some pos) =>
            match payload input pos with
            | some (header,_) => if pos+header == id then n else rootPathLength input path id fuel n
            | none => rootPathLength input path id fuel n
        | _ => rootPathLength input path id fuel n
      else rootPathLength input path id fuel n

def rootKey (path : Array UInt8) (baseLength : Nat) : Value :=
  if path.size ≤ 1 || baseLength == path.size then .null
  else if byte path baseLength == 91 then
    .integer (Numeric.integer (Text.fromBytes (path.extract (baseLength+1) (path.size-1))))
  else if byte path (baseLength+1) == 34 then
    Text.fromBytes (path.extract (baseLength+2) (path.size-1))
  else Text.fromBytes (path.extract (baseLength+1) path.size)

def row (input : Array UInt8) (recursive : Bool) (entry : Entry) : Except String (List Value) := do
  let kind := byte input entry.pos % 16
  let scalar ← JsonExtract.valueAt input entry.pos
  let value ← if kind == 11 || kind == 12 then pure (← JsonText.render input entry.pos).value else pure scalar
  return [entry.key,value,.text (JsonAccess.typeName kind),
    if kind == 11 || kind == 12 then .null else scalar,
    .integer entry.id, if recursive then (entry.parent.map (fun n => Value.integer n)).getD .null else .null,
    Text.fromBytes entry.fullkey,Text.fromBytes entry.path]

def walk (input : Array UInt8) (recursive : Bool) : Nat → List Entry → Except String (List (List Value))
  | 0, _ => .error "malformed JSON"
  | _+1, [] => .ok []
  | fuel+1, entry :: rest => do
      let value ← row input recursive entry
      let next ← if recursive then pure ((← children input entry) ++ rest) else pure rest
      return value :: (← walk input recursive fuel next)

def evaluate (recursive : Bool) (value : Value) (pathValue : Option Value := none) :
    Except String (List (List Value)) := do
  let encoded ← JsonBinary.evaluate value
  let .blob input := encoded | return []
  let some selected ← JsonAccess.select input pathValue | return []
  let path := match pathValue with
    | none => "$".toUTF8.data
    | some value => JsonExtract.nulPrefix (Text.bytes value)
  let original : Entry := { id := 0, pos := 0, fullkey := "$".toUTF8.data, path := "$".toUTF8.data }
  let found ← findEntry input selected (4*input.size+4) [original]
  let baseLength := if recursive then rootPathLength input path found.id (path.size+1) path.size else path.size
  let root : Entry := { found with
    key := rootKey path baseLength
    fullkey := path
    path := path.extract 0 baseLength
    parent := none }
  let initial ← if recursive then pure [root] else do
    let kind := byte input selected % 16
    if kind == 11 || kind == 12 then children input root else pure [root]
  walk input recursive (4*input.size+4) initial

theorem evaluate_null (recursive : Bool) (path : Option Value) :
    evaluate recursive .null path = .ok [] := by
  simp [evaluate, JsonBinary.evaluate_null, bind, Except.bind, pure, Except.pure]

end SQLeanite.SQLite.JsonTable
