import SQLeanite.SyscallVFS
import Std.Data.HashMap

namespace SQLeanite.Runtime.ReadPager

/-- Read-transaction page cache. Like SQLite's pager/pcache boundary, this
layer knows page numbers and byte buffers, not schemas, rows, or SQL. The
current host backend uses the existing reviewed positional-read binding.
A pager/cache belongs to one immutable snapshot; discard it before writes. -/
structure Pager where
  readAt : UInt64 → USize → IO ByteArray
  pageCount : Nat
  pageSize : Nat
  pages : IO.Ref (Std.HashMap Nat ByteArray)
  capacity : Nat

def ofPath (path : System.FilePath) (pageCount pageSize : Nat)
    (pages : IO.Ref (Std.HashMap Nat ByteArray)) (capacity : Nat) : Pager := {
  readAt := SyscallVFS.preadBytes path.toString
  pageCount, pageSize, pages, capacity }

def create (path : System.FilePath) (pageCount pageSize : Nat)
    (capacity : Nat := 512) : IO Pager := do
  return ofPath path pageCount pageSize
    (← IO.mkRef (Std.HashMap.emptyWithCapacity capacity)) capacity

/-- Fetch a complete page, retaining at most `capacity` buffers. Saturation
changes only caching, never lookup results. Short reads are rejected. -/
def Pager.get (pager : Pager) (pageNumber : Nat) : IO (Option ByteArray) := do
  if pageNumber = 0 ∨ pager.pageCount < pageNumber then return none
  let pages ← pager.pages.get
  match pages.get? pageNumber with
  | some page => return some page
  | none =>
      let bytes ← pager.readAt
        (UInt64.ofNat ((pageNumber - 1) * pager.pageSize))
        (USize.ofNat pager.pageSize)
      unless bytes.size = pager.pageSize do return none
      if pages.size < pager.capacity then
        pager.pages.set (pages.insert pageNumber bytes)
      return some bytes

end SQLeanite.Runtime.ReadPager
