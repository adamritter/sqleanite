import SQLeanite.SyscallVFS

/-! Linux OFD byte-range locks conflict with SQLite's POSIX locks and survive
other helpers closing separate descriptors for the same inode. The native
layer contains no WAL/index algorithms. -/
namespace SQLeanite.WALVFS

@[extern "sqleanite_try_range_lock"]
opaque tryRangeLock (path : @& String) (offset length : UInt64)
    (exclusive create : Bool) : IO (Option USize)

@[extern "sqleanite_release_range_lock"]
opaque releaseRangeLock (descriptor : USize) : IO Unit

@[extern "sqleanite_native_big_endian"]
opaque nativeBigEndian : IO Bool

def withRange (path : System.FilePath) (offset length : Nat)
    (exclusive create : Bool) (action : IO α) : IO α := do
  let some descriptor ← tryRangeLock path.toString offset.toUInt64 length.toUInt64
      exclusive create | throw (IO.userError "database is locked")
  try action finally releaseRangeLock descriptor

end SQLeanite.WALVFS
