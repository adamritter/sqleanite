import SQLeanite.FileFormat

/-! btree.c:lockBtree and pager.c:pagerPagecount. A nonzero header page count
is authoritative only when its change counter equals version-valid-for. Older
writers leave that size unset or stale, requiring the rounded-up file size. -/
namespace SQLeanite.SQLite.DatabaseSize

def filePages (bytes pageSize : Nat) : Nat := (bytes + pageSize - 1) / pageSize

def headerSizeValid (header : FileFormat.DatabaseHeader) : Bool :=
  header.databaseSizePages.val != 0 &&
    header.headerPrefix.changeCounter.val == header.versionValidFor.val

def pageCount (header : FileFormat.DatabaseHeader) (bytes pageSize : Nat) : Nat :=
  if headerSizeValid header then header.databaseSizePages.val else filePages bytes pageSize

/-- A trusted size past physical EOF is corrupt. Unreferenced physical tail
bytes/pages are permitted when a current header specifies a smaller image. -/
def pageCount? (header : FileFormat.DatabaseHeader) (bytes pageSize : Nat) : Option Nat :=
  let count := pageCount header bytes pageSize
  if pageSize > 0 && count > 0 && count ≤ filePages bytes pageSize then some count else none

/-- SQLite's ordinary VFS short read zero-fills a final partial page. A page
starting at or beyond EOF is absent and cannot be supplied by the base file. -/
def pageBytes (input : ByteArray) (pageSize pageNumber : Nat) : Option (List UInt8) :=
  if pageSize == 0 || pageNumber == 0 then none
  else
    let start := (pageNumber - 1) * pageSize
    if start ≥ input.size then none
    else
      let bytes := input.extract start (start + pageSize)
      some (bytes.toList ++ List.replicate (pageSize - bytes.size) 0)

theorem pageCount_zero (header : FileFormat.DatabaseHeader) (bytes pageSize : Nat)
    (zero : header.databaseSizePages.val = 0) :
    pageCount header bytes pageSize = filePages bytes pageSize := by
  simp [pageCount, headerSizeValid, zero]

theorem pageCount_stale (header : FileFormat.DatabaseHeader) (bytes pageSize : Nat)
    (stale : header.headerPrefix.changeCounter.val ≠ header.versionValidFor.val) :
    pageCount header bytes pageSize = filePages bytes pageSize := by
  simp [pageCount, headerSizeValid, stale]

theorem pageCount_current (header : FileFormat.DatabaseHeader) (bytes pageSize : Nat)
    (nonzero : header.databaseSizePages.val ≠ 0)
    (current : header.headerPrefix.changeCounter.val = header.versionValidFor.val) :
    pageCount header bytes pageSize = header.databaseSizePages.val := by
  simp [pageCount, headerSizeValid, nonzero, current]

end SQLeanite.SQLite.DatabaseSize
