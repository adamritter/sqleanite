import SQLeanite.PhysicalQuery

/-! The pinned main.c BINARY, NOCASE and RTRIM byte comparators. This module
compares TEXT bytes; other storage classes keep the physical numeric ordering. -/
namespace SQLeanite.SQLite.Collation

inductive Kind where
  | binary | nocase | rtrim
  deriving Repr, BEq, DecidableEq

def named? (name : String) : Option Kind :=
  match name.toLower with
  | "binary" => some .binary
  | "nocase" => some .nocase
  | "rtrim" => some .rtrim
  | _ => none

def lower (byte : UInt8) : UInt8 :=
  if 65 ≤ byte.toNat && byte.toNat ≤ 90 then byte + 32 else byte

/-- sqlite3StrNICmp stops at NUL or the shorter supplied byte length. -/
def noCasePrefix : List UInt8 → List UInt8 → Ordering
  | [], _ | _, [] => .eq
  | a :: as, b :: bs =>
      let order := compare (lower a) (lower b)
      if order != .eq then order
      else if a == 0 then .eq else noCasePrefix as bs

def rtrimBytes (bytes : List UInt8) : List UInt8 :=
  (bytes.reverse.dropWhile (· == 32)).reverse

def compareText (kind : Kind) (left right : List UInt8) : Ordering :=
  match kind with
  | .binary => compare left right
  | .rtrim => compare (rtrimBytes left) (rtrimBytes right)
  | .nocase =>
      let order := noCasePrefix left right
      if order == .eq then compare left.length right.length else order

def compareValue (kind : Kind) (left right : PhysicalCodec.Value) : Ordering :=
  match left, right with
  | .text a, .text b => compareText kind a.bytes b.bytes
  | _, _ => PhysicalQuery.compareValue left right

/-- Collation changes TEXT comparison, while SQL NULL propagation remains
independent of the comparison kind. -/
def sqlEquals (kind : Kind) : PhysicalCodec.Value → PhysicalCodec.Value → Truth
  | .null, _ | _, .null => .unknown
  | left, right => if compareValue kind left right == .eq then .true else .false

def sqlCompare (kind : Kind) (operation : PhysicalQuery.Comparison) :
    PhysicalCodec.Value → PhysicalCodec.Value → Truth
  | .null, _ | _, .null => .unknown
  | left, right => if operation.holds (compareValue kind left right) then .true else .false

theorem noCasePrefix_self (bytes : List UInt8) : noCasePrefix bytes bytes = .eq := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih => simp [noCasePrefix, ih]

theorem compareText_self (kind : Kind) (bytes : List UInt8) : compareText kind bytes bytes = .eq := by
  cases kind <;> simp [compareText, noCasePrefix_self]

theorem noCase_nul (left right : List UInt8) :
    compareText .nocase (0 :: left) (0 :: right) = compare (left.length + 1) (right.length + 1) := by
  simp [compareText, noCasePrefix]

theorem rtrimBytes_space (bytes : List UInt8) :
    rtrimBytes (bytes ++ [32]) = rtrimBytes bytes := by
  simp [rtrimBytes]

end SQLeanite.SQLite.Collation
