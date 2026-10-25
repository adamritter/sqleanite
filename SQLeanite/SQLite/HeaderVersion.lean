import SQLeanite.FileFormat

namespace SQLeanite.SQLite.HeaderVersion

/-- lockBtree accepts historical zero bytes as well as versions one and two.
An unknown read version prevents opening even when no SQL rows are requested. -/
def formatReadError? (header : FileFormat.DatabaseHeader) : Option String :=
  if 2 < header.headerPrefix.readVersion.toNat then some "file is not a database" else none

/-- An unknown write version admits readers but forbids a write transaction. -/
def formatWriteError? (header : FileFormat.DatabaseHeader) : Option String :=
  (formatReadError? header).orElse fun _ =>
    if 2 < header.headerPrefix.writeVersion.toNat then
      some "attempt to write a readonly database" else none

/-- sqlite3InitOne narrows the schema-format metadata to u8; zero then denotes
format one. Preserve that pinned behavior for high metadata bits as well. -/
def schemaError? (header : FileFormat.DatabaseHeader) : Option String :=
  if 4 < header.schemaFormat.val % 256 then some "unsupported file format" else none

def readError? (header : FileFormat.DatabaseHeader) : Option String :=
  (formatReadError? header).orElse fun _ => schemaError? header

def writeError? (header : FileFormat.DatabaseHeader) : Option String :=
  (readError? header).orElse fun _ => formatWriteError? header

theorem unknown_read {header : FileFormat.DatabaseHeader}
    (unknown : 2 < header.headerPrefix.readVersion.toNat) :
    readError? header = some "file is not a database" := by
  simp [readError?, formatReadError?, unknown]

theorem unknown_write {header : FileFormat.DatabaseHeader}
    (readable : readError? header = none)
    (unknown : 2 < header.headerPrefix.writeVersion.toNat) :
    writeError? header = some "attempt to write a readonly database" := by
  unfold readError? at readable
  cases decoded : formatReadError? header <;> simp_all [writeError?, readError?, formatWriteError?]

theorem schema_low_byte {left right : FileFormat.DatabaseHeader}
    (same : left.schemaFormat.val % 256 = right.schemaFormat.val % 256) :
    schemaError? left = schemaError? right := by
  simp [schemaError?, same]

end SQLeanite.SQLite.HeaderVersion
