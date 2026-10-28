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

/-- A source's actual rowid and column range within a joined evaluation row. -/
structure StoredText.Source where
  table : String
  rowidColumn : Nat
  offset : Nat
  width : Nat

end SQLeanite.SQLite
