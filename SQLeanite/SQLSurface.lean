import SQLeanite.Parser
import SQLeanite.PhysicalCodec

/-!
# Shared SQL value surface

Translation from parsed SQL literals to physical storage values. Both the
arbitrary-schema core (`CoreSQL`) and the legacy fixed-schema path
(`LegacyFixedSQL`) need this, and nothing here depends on either engine.

Extracting it is what lets `CoreSQL` stop importing `LegacyFixedSQL`, which
previously dragged the whole fixed-schema engine into the core's dependency
cone for a single function.
-/

namespace SQLeanite.SQLSurface

def unsupported (feature : String) : Except String α :=
  .error s!"unsupported verified-MVP SQL: {feature}"

def signed64 (value : Int) : Except String (FileFormat.SignedInteger .eight) :=
  if lower : -(Int.ofNat FileFormat.IntegerWidth.eight.midpoint) ≤ value then
    if upper : value < Int.ofNat FileFormat.IntegerWidth.eight.midpoint then
      .ok ⟨value, lower, upper⟩
    else .error "MVP INTEGER is above signed 64-bit range"
  else .error "MVP INTEGER is below signed 64-bit range"

def value (input : SQLeanite.Value) : Except String PhysicalCodec.Value :=
  match input with
  | .null => .ok .null
  | .integer integer => .integer <$> signed64 integer
  | .text string =>
      let bytes := string.toUTF8.data.toList
      if bound : bytes.length < PhysicalCodec.textByteLimit then
        .ok (.text ⟨bytes, bound⟩)
      else .error "MVP TEXT exceeds the 999-byte limit"
  | .real value =>
      if value.isNaN then unsupported "NaN REAL value"
      else
        let bits := value.toBits
        .ok (.realBits ⟨bits.toNat, by simpa using bits.toNat_lt⟩)
  | .blob bytes =>
      let payload := bytes.toList
      if bound : payload.length < PhysicalCodec.textByteLimit then
        .ok (.blob ⟨payload, bound⟩)
      else .error "MVP BLOB exceeds the 999-byte local-page limit"

def literal : Expr → Except String PhysicalCodec.Value
  | .literal input => value input
  | .unary .plus expression => literal expression
  | .unary .neg expression => do
      let decoded ← literal expression
      match decoded with
      | .integer integer => .integer <$> signed64 (-integer.value)
      | _ => unsupported "unary minus on non-INTEGER literal"
  | _ => unsupported "non-literal INSERT value"

end SQLeanite.SQLSurface
