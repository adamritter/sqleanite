import SQLeanite.CoreDecode.IndexPayloadIO
import SQLeanite.CoreIndexKey

/-! Pointer-directed physical index traversal for arbitrary key counts. Pure
and IO acquisition share the same header, child, cell-order and fuel decisions. -/
namespace SQLeanite.CoreDecode.IndexRecords
open FileFormat

def recordValues (encoding payloadSize : Nat) (payload : List UInt8) : Option (List Core.Value) := do
  let (record,suffix) ← decodePhysicalRecord payload
  unless suffix.isEmpty && record.encode.length == payloadSize do none
  let fields ← CoreTextEncoding.fields encoding record.fields
  fields.mapM PhysicalCodec.decodeValueField

def recordEntry (encoding payloadSize : Nat) (payload : List UInt8) : Option CoreIndexKey.Entry := do
  CoreIndexKey.fromValues (← recordValues encoding payloadSize payload)

def cellFrom (source : PageSource) (input : List UInt8) : Option CoreIndexKey.Entry := do
  let (size,afterSize) ← decodeVarint input
  let (payload,_) ← decodeIndexPayloadBytesFrom source (source.pageCount+1) size.val afterSize
  recordEntry 1 size.val payload

def cellIOFrom (source : IOPageSource) (input : List UInt8) : IO (Option CoreIndexKey.Entry) := do
  let some (cell,_) := decodeLeafIndexCell source.usable input | return none
  let some payload ← resolvedIndexPayloadIOFrom source (source.pageCount+1) cell | return none
  return recordEntry source.textEncoding cell.payloadSize.val payload

def subtreeWith {α : Type} [Monad m] (size : Nat) (readPage : Nat → m (Option (List UInt8)))
    (readCell : List UInt8 → m (Option α)) :
    Nat → Nat → m (Option (List α))
  | 0, _ => pure none
  | fuel+1, pageNumber => do
      let some page ← readPage pageNumber | return none
      unless page.length == size do return none
      let some (header,afterHeader) := decodeBTreePageHeader page | return none
      match header with
      | .leafIndex common =>
          let some (offsets,_) := decodeOffsets common.cellCount.val afterHeader | return none
          let cells ← offsets.mapM fun offset => do
            unless offset < page.length do return none
            readCell (page.drop offset)
          return sequenceOptions cells
      | .interiorIndex common rightmost =>
          let some (offsets,_) := decodeOffsets common.cellCount.val afterHeader | return none
          let groups ← offsets.mapM fun offset => do
            unless offset < page.length do return none
            let some (child,afterChild) := decodeUnsignedFixed 4 (page.drop offset) | return none
            let some key ← readCell afterChild | return none
            let some left ← subtreeWith size readPage readCell fuel child | return none
            return some (left ++ [key])
          let some groups := sequenceOptions groups | return none
          let some right ← subtreeWith size readPage readCell fuel rightmost.val | return none
          return some (groups.flatten ++ right)
      | _ => return none

def subtreeFrom (source : PageSource) (fuel rootPage : Nat) : Option (List CoreIndexKey.Entry) :=
  Id.run (subtreeWith PhysicalCodec.pageSize (fun page => pure (source.readPage page))
    (fun input => pure (cellFrom source input)) fuel rootPage)

def subtreeIOFrom (source : IOPageSource) (fuel rootPage : Nat) : IO (Option (List CoreIndexKey.Entry)) :=
  subtreeWith source.usable.val source.readPage (cellIOFrom source) fuel rootPage

def cellValuesFrom (source : PageSource) (input : List UInt8) : Option (List Core.Value) := do
  let (size,afterSize) ← decodeVarint input
  let (payload,_) ← decodeIndexPayloadBytesFrom source (source.pageCount+1) size.val afterSize
  recordValues 1 size.val payload

def cellValuesIOFrom (source : IOPageSource) (input : List UInt8) : IO (Option (List Core.Value)) := do
  let some (cell,_) := decodeLeafIndexCell source.usable input | return none
  let some payload ← resolvedIndexPayloadIOFrom source (source.pageCount+1) cell | return none
  return recordValues source.textEncoding cell.payloadSize.val payload

def valuesFrom (source : PageSource) (fuel rootPage : Nat) : Option (List (List Core.Value)) :=
  Id.run (subtreeWith PhysicalCodec.pageSize (fun page => pure (source.readPage page))
    (fun input => pure (cellValuesFrom source input)) fuel rootPage)

def valuesIOFrom (source : IOPageSource) (fuel rootPage : Nat) : IO (Option (List (List Core.Value))) :=
  subtreeWith source.usable.val source.readPage (cellValuesIOFrom source) fuel rootPage

end SQLeanite.CoreDecode.IndexRecords
