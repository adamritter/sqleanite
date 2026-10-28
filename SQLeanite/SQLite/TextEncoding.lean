import SQLeanite.SQLite.Text
import SQLeanite.Syntax

/-! SQLite utf.c byte translations. Internal TEXT remains exact UTF-8 bytes;
UTF-16 storage and encoding-dependent functions use the actual database cookie.
The pinned SQLite build does not define SQLITE_REPLACE_INVALID_UTF. -/
namespace SQLeanite.SQLite.TextEncoding

def supported (encoding : Nat) : Bool := encoding ≤ 3

def utf8 (code : Nat) : List UInt8 :=
  if code < 128 then [UInt8.ofNat code]
  else if code < 2048 then [UInt8.ofNat (192 + code / 64),UInt8.ofNat (128 + code % 64)]
  else if code < 65536 then [UInt8.ofNat (224 + code / 4096),UInt8.ofNat (128 + code / 64 % 64),UInt8.ofNat (128 + code % 64)]
  else [UInt8.ofNat (240 + code / 262144),UInt8.ofNat (128 + code / 4096 % 64),UInt8.ofNat (128 + code / 64 % 64),UInt8.ofNat (128 + code % 64)]

def unit (big : Bool) (first second : UInt8) : Nat :=
  if big then first.toNat * 256 + second.toNat else first.toNat + second.toNat * 256

/-- An odd trailing byte is discarded by sqlite3VdbeMemTranslate. Its default
surrogate branch consumes the next code unit whenever one is available. -/
def decode16Fuel (big : Bool) : Nat → List UInt8 → List UInt8
  | 0, _ => []
  | fuel + 1, first :: second :: rest =>
      let code := unit big first second
      if 55296 ≤ code && code < 57344 then
        match rest with
        | third :: fourth :: tail =>
            let next := unit big third fourth
            utf8 ((next % 1024) + (code % 64) * 1024 + ((code / 64 % 16) * 64 + 64) * 1024) ++ decode16Fuel big fuel tail
        | _ => utf8 code ++ decode16Fuel big fuel rest
      else utf8 code ++ decode16Fuel big fuel rest
  | _, _ => []

def decode16 (big : Bool) (bytes : List UInt8) : List UInt8 :=
  decode16Fuel big bytes.length bytes

def encodeUnit (big : Bool) (code : Nat) : List UInt8 :=
  let low := UInt8.ofNat code
  let high := UInt8.ofNat (code / 256)
  if big then [high,low] else [low,high]

def encodeCode (big : Bool) (code : Nat) : List UInt8 :=
  if code < 65536 then encodeUnit big code else
    encodeUnit big (55296 + ((code - 65536) / 1024) % 1024) ++ encodeUnit big (56320 + code % 1024)

def encode16 (big : Bool) (bytes : Array UInt8) : Array UInt8 :=
  ((Text.codepointsFuel false bytes.size bytes.toList).flatMap (encodeCode big)).toArray

def fromStorage (encoding : Nat) (bytes : Array UInt8) : Array UInt8 :=
  if encoding == 2 || encoding == 3 then (decode16 (encoding == 3) bytes.toList).toArray else bytes

def toStorage (encoding : Nat) (bytes : Array UInt8) : Array UInt8 :=
  if encoding == 2 || encoding == 3 then encode16 (encoding == 3) bytes else bytes

/-- Read-time reencoding for strict, unary SQL operations. All arguments are
ordinary evaluated values; NULL and BLOB retain their original classes. -/
def builtin (function : String) (encoding : Nat) (value : Value) : Except String Value := do
  let encoded := fun value => toStorage encoding (Text.bytes value)
  match function with
  | "hex" => Text.hex (.blob (match value with | .blob bytes => bytes | _ => encoded value))
  | "octet_length" => match value with
      | .null => return .null
      | .blob bytes => return .integer bytes.size
      | _ => return .integer (encoded value).size
  | "cast_blob" => match value with
      | .null => return .null
      | .blob _ => return value
      | _ => return .blob (encoded value)
  | "cast_text" => match value with
      | .null => return .null
      | .blob bytes => Text.checkedBytes (fromStorage encoding bytes)
      | .text _ | .textBytes _ => return value
      | _ => Text.checkedBytes (Text.bytes value)
  | _ => throw "invalid encoded scalar operation"

/-- Ordinary UTF-8 callers keep the original AST and evaluator. -/
def bind : Nat → Nat → Expr → Expr
  | _, 0, expression => expression
  | encoding, fuel + 1, expression =>
      if encoding != 2 && encoding != 3 then expression else
      let visit := bind encoding fuel
      match expression with
      | .call "__sqlean_encoded" _ _ => expression
      | .call "__sqlean_between" arguments false =>
          .call "__sqlean_between" (arguments.map visit) false
      | .call "__sqlean_aggregate_filter" #[.call name arguments star,predicate] false =>
          .call "__sqlean_aggregate_filter" #[.call name (arguments.map visit) star,visit predicate] false
      | .call "__sqlean_window" #[function,metadata] false =>
          let function := match function with
            | .call "__sqlean_aggregate_filter" #[.call name arguments star,predicate] false =>
                .call "__sqlean_aggregate_filter" #[.call name (arguments.map visit) star,visit predicate] false
            | .call name arguments star => .call name (arguments.map visit) star
            | other => visit other
          .call "__sqlean_window" #[function,metadata] false
      | .call "__sqlean_declared_collation" #[argument,metadata] false =>
          .call "__sqlean_declared_collation" #[visit argument,metadata] false
      | .call "__sqlean_bound_value" #[argument,metadata] false =>
          .call "__sqlean_bound_value" #[visit argument,metadata] false
      | .column .. | .literal (.text _) _ | .literal (.textBytes _) _ =>
          .call "__sqlean_encoded" #[.literal (.text "input"),.literal (.integer encoding),expression] false
      | .call name arguments star =>
          let arguments := arguments.map visit
          if !star && arguments.size == 1 && ["hex","octet_length","cast_blob","cast_text"].contains name.toLower then
            .call "__sqlean_encoded" #[.literal (.text name.toLower),.literal (.integer encoding),arguments[0]!] false
          else .call "__sqlean_encoded" #[.literal (.text "context"),.literal (.integer encoding),.call name arguments star] false
      | .unary op arg => .unary op (visit arg)
      | .binary .concat a b =>
          .call "__sqlean_encoded" #[.literal (.text "input"),.literal (.integer encoding),.binary .concat (visit a) (visit b)] false
      | .binary op a b => .binary op (visit a) (visit b)
      | .isNull arg negated => .isNull (visit arg) negated
      | .inList arg values negated affinity => .inList (visit arg) (values.map visit) negated affinity
      | .collate arg name => .collate (visit arg) name
      | .case_ base branches other => .case_ (base.map visit) (branches.map fun (a,b) => (visit a,visit b)) (other.map visit)
      | .inSubquery arg sql negated => .inSubquery (visit arg) sql negated
      | .scalarSubquery _ =>
          .call "__sqlean_encoded" #[.literal (.text "context"),.literal (.integer encoding),expression] false
      | other => other

theorem fromStorage_utf8 (bytes : Array UInt8) : fromStorage 1 bytes = bytes := rfl

theorem toStorage_utf8 (bytes : Array UInt8) : toStorage 1 bytes = bytes := rfl

theorem bind_utf8 (fuel : Nat) (expression : Expr) : bind 1 fuel expression = expression := by
  cases fuel <;> rfl

theorem decode16_single (big : Bool) (byte : UInt8) : decode16 big [byte] = [] := rfl

end SQLeanite.SQLite.TextEncoding
