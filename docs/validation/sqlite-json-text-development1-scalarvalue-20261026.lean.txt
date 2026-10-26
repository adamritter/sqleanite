import SQLeanite.Value

namespace SQLeanite.SQLite

/-- Subtype belongs to an evaluated SQL value, independently of storage class. -/
structure ScalarValue where
  value : Value
  subtype : UInt8 := 0

end SQLeanite.SQLite
