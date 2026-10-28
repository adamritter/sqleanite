import SQLeanite.Value

namespace SQLeanite.SQLite

/-- Subtype belongs to an evaluated SQL value, independently of storage class. -/
structure ScalarValue where
  value : Value
  subtype : UInt8 := 0
  /-- Current runtime text representation; storage class and subtype are independent. -/
  textEncoding : Nat := 1
  /-- A CAST from BLOB can retain malformed/odd UTF-16 bytes until converted. -/
  encodedText : Option (Array UInt8) := none

end SQLeanite.SQLite
