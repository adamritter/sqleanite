import SQLeanite.Value

namespace SQLeanite.SQLite

/-- Native storage representation retained when UTF-16 to UTF-8 conversion is
not reversible. Row and column identity refer to the actual decoded record. -/
structure StoredText where
  table : String
  rowid : Int
  column : Nat
  encoding : Nat
  bytes : Array UInt8

end SQLeanite.SQLite
