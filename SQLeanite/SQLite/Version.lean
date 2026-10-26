import SQLeanite.Syntax

/-! SQL-visible identifiers of the repository's pinned SQLite compatibility
target. These do not identify SQLeanite's own source revision or its completed
feature coverage. The implementation contains no SQLite C dependency. -/
namespace SQLeanite.SQLite.Version

def number : String := "3.53.4"
def source : String := "2026-07-24 19:02:57 bf7c7f30031888f4e796e429ab3978879485813aaca6f641c7b33e4e09459bcc"

def value? (name : String) : Option Value :=
  if name == "sqlite_version" then some (.text number)
  else if name == "sqlite_source_id" then some (.text source)
  else none

def recognizes (name : String) : Bool := (value? name).isSome

theorem version_value : value? "sqlite_version" = some (.text number) := rfl
theorem source_value : value? "sqlite_source_id" = some (.text source) := rfl

end SQLeanite.SQLite.Version
