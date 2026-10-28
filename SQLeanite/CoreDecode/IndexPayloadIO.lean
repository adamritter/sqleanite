import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeAbstractTableTreeFromToList

namespace SQLeanite.CoreDecode
open FileFormat

def resolvedIndexPayloadIOFrom (source : IOPageSource) (fuel : Nat)
    (cell : LeafIndexCell source.usable) :
    IO (Option (List UInt8)) :=
  match cell.payload.data with
  | .inline bytes => pure (some bytes)
  | .overflow localBytes first => do
      let remaining := cell.payloadSize.val - localBytes.length
      let some rest ← readOverflowIOFrom source fuel remaining first.value.val |
        return none
      return some (localBytes ++ rest)

end SQLeanite.CoreDecode
