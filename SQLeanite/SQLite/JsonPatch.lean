import SQLeanite.SQLite.JsonExtract

namespace SQLeanite.SQLite.JsonPatch
open JsonValid

structure Edit where
  bytes : Array UInt8
  delta : Int

/-- During edits SQLite also admits payloads ending within the pre-edit span. -/
def payloadEdited (input : Array UInt8) (delta : Int) (pos : Nat) : Option (Nat × Nat) := do
  unless pos < input.size do none
  let first := byte input pos / 16
  let width := if first ≤ 11 then 0 else if first == 12 then 1 else if first == 13 then 2 else if first == 14 then 4 else 8
  unless pos+width < input.size do none
  if width == 8 && !((List.range 4).all (fun i => byte input (pos+i+1) == 0)) then none
  let count := if width == 0 then first else
    (List.range width).foldl (fun n i => n*256 + byte input (pos+i+1)) 0
  unless pos+width+1+count ≤ max input.size (Int.ofNat input.size-delta).toNat do none
  return (width+1,count)

def enlarged (input : Array UInt8) (extra : Nat) : Option (Array UInt8) := do
  unless 0 < extra && extra ≤ 8 && byte input 0 % 16 > 2 do none
  let first := byte input 0 / 16
  let old := if first ≤ 11 then 1 else if first == 12 then 2 else if first == 13 then 3 else if first == 14 then 5 else 9
  let new := old+extra
  unless [2,3,5,9].contains new && old ≤ input.size do none
  let kind := byte input 0 % 16
  let header := if new == 2 then 12 else if new == 3 then 13 else if new == 5 then 14 else 15
  let size := input.size-old
  return #[UInt8.ofNat (header*16+kind)] ++
    (List.range (new-1)).toArray.map (fun i => UInt8.ofNat (size / 256^(new-2-i) % 256)) ++
    input.extract old input.size

def edit (input : Array UInt8) (pos count : Nat) (insert : Array UInt8)
    (overwrite : Bool) : Edit := Id.run do
  let insert := if overwrite && insert.size < count then
      (enlarged insert (count-insert.size)).getD insert else insert
  return ⟨input.extract 0 pos ++ insert ++ input.extract (pos+count) input.size,
    Int.ofNat insert.size - Int.ofNat count⟩

structure Member where
  label : Nat
  value : Nat
  finish : Nat

def findMember (input : Array UInt8) (delta : Int) (key : Array UInt8) (raw : Bool)
    (finish : Nat) : Nat → Nat → Except String (Option Member)
  | 0, _ => .error "malformed JSON"
  | fuel+1, pos => do
      if pos ≥ finish then return none
      let kind := byte input pos % 16
      unless 7 ≤ kind && kind ≤ 10 do throw "malformed JSON"
      let (header,size) ← JsonAccess.require "malformed JSON" (payloadEdited input delta pos)
      let value := pos+header+size
      if value ≥ finish then throw "malformed JSON"
      let (vheader,vsize) ← JsonAccess.require "malformed JSON" (payloadEdited input delta value)
      let next := value+vheader+vsize
      if next > finish then throw "malformed JSON"
      if JsonAccess.labelEqual key (input.extract (pos+header) value) raw (kind == 7 || kind == 10) then
        return some ⟨pos,value,next⟩
      findMember input delta key raw finish fuel next

mutual
  def merge (input patch : Array UInt8) (target source depth : Nat) : Nat → Except String Edit
    | 0 => .error "JSON nested too deep"
    | fuel+1 => do
        let (pheader,psize) := (payload patch source).getD (0,0)
        let (header,size) := (payload input target).getD (0,0)
        if byte patch source % 16 != 12 then
          return edit input target (header+size) (patch.extract source (source+pheader+psize)) true
        let mut edited := Edit.mk input 0
        if byte input target % 16 != 12 then
          edited := edit input (target+header) size #[] false
          edited := { edited with bytes := edited.bytes.set! target (UInt8.ofNat ((byte input target / 16)*16+12)) }
        if pheader == 0 || header == 0 then throw "malformed JSON"
        let done ← members patch depth (target+header) (target+header+size)
          (source+pheader+psize) fuel (source+pheader) edited
        if done.delta == 0 then return done
        let updated := ((Int.ofNat size+done.delta) % (2^32)).toNat
        let replacement := JsonExtract.reservedHeader 12 updated
        let resized := edit done.bytes target header replacement false
        return { resized with delta := done.delta+resized.delta }
  def members (patch : Array UInt8) (depth targetStart targetEnd patchEnd : Nat) :
      Nat → Nat → Edit → Except String Edit
    | 0, _, _ => .error "JSON nested too deep"
    | fuel+1, pos, edited => do
        if pos ≥ patchEnd then return edited
        let kind := byte patch pos % 16
        unless 7 ≤ kind && kind ≤ 10 do throw "malformed JSON"
        let (header,size) ← JsonAccess.require "malformed JSON" (payload patch pos)
        let value := pos+header+size
        if value ≥ patchEnd then throw "malformed JSON"
        let (vheader,vsize) ← JsonAccess.require "malformed JSON" (payload patch value)
        let next := value+vheader+vsize
        if next > patchEnd then throw "malformed JSON"
        let finish := (Int.ofNat targetEnd+edited.delta).toNat
        let found ← findMember edited.bytes edited.delta (patch.extract (pos+header) value)
          (kind == 7 || kind == 10) finish (edited.bytes.size+1) targetStart
        let valueKind := byte patch value % 16
        let changed ← match found with
          | some member => do
              if valueKind == 0 then
                pure (edit edited.bytes member.label (member.finish-member.label) #[] false)
              else
                if depth ≥ 1000 then throw "JSON nested too deep"
                merge edited.bytes patch member.value value (depth+1) fuel
          | none => do
              if valueKind == 0 then pure ⟨edited.bytes,0⟩
              else if valueKind != 12 then
                pure (edit edited.bytes finish 0 (patch.extract pos next) false)
              else
                let inserted := edit edited.bytes finish 0 (patch.extract pos value ++ #[0]) false
                if depth ≥ 1000 then throw "JSON nested too deep"
                let result ← merge inserted.bytes patch (finish+header+size) value (depth+1) fuel
                pure { result with delta := result.delta+inserted.delta }
        members patch depth targetStart targetEnd patchEnd fuel next
          { changed with delta := changed.delta+edited.delta }
end

def evaluate (target patch : Value) : Except String Value := do
  let target ← JsonBinary.evaluate target
  let .blob input := target | return .null
  let patch ← JsonBinary.evaluate patch
  let .blob patch := patch | return .null
  let result ← merge input patch 0 0 0 (4*(input.size+patch.size+1))
  return .blob result.bytes

theorem evaluate_null (patch : Value) : evaluate .null patch = .ok .null := rfl

theorem evaluate_null_patch (target : Value) (input : Array UInt8)
    (loaded : JsonBinary.evaluate target = .ok (.blob input)) :
    evaluate target .null = .ok .null := by
  simp only [evaluate, loaded, JsonBinary.evaluate_null] <;> rfl

theorem enlarged_zero (input : Array UInt8) : enlarged input 0 = none := by
  simp [enlarged]

theorem findMember_end (input key : Array UInt8) (delta : Int) (raw : Bool)
    (finish fuel pos : Nat) (done : finish ≤ pos) :
    findMember input delta key raw finish (fuel+1) pos = .ok none := by
  simp [findMember, done, pure, Except.pure]

end SQLeanite.SQLite.JsonPatch
