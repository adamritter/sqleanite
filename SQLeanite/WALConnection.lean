import SQLeanite.WALConcurrency
import SQLeanite.CoreSQL
import Std.Sync.Mutex

namespace SQLeanite

/-!
# Runtime WAL connection shell

This is an unverified adapter for the pure model in `WALConcurrency`.  Readers
retain an immutable published `Core.Database` and evaluate without holding a lock.
A separate writer lock admits one writer, which computes a private next value
and publishes it under the short WAL-state lock.
-/

structure WALConnection where
  private state : Std.Mutex WALConcurrency.WAL
  private writerLock : Std.BaseMutex

namespace WALConnection

def create (initial : Core.Database := Core.Database.empty) : BaseIO WALConnection := do
  return {
    state := ← Std.Mutex.new { main := initial }
    writerLock := ← Std.BaseMutex.new
  }

/-- Copy the currently published immutable database. -/
def snapshot (connection : WALConnection) : IO Core.Database :=
  connection.state.atomically do
    return (← get).visible

/-- Evaluate a read against a retained snapshot without holding either lock.
Any database changes produced by the SQL text are intentionally discarded; the
runtime API treats this operation as read-only. -/
def executeRead (connection : WALConnection) (sql : String) :
    IO (Except String (List Core.Result)) := do
  let database ← connection.snapshot
  match CoreSQL.execute { database := database } sql with
  | .error message => return .error message
  | .ok (_, results) => return .ok results

/-- Serialize writers, compute the next immutable value without blocking
readers, then publish one durable logical WAL frame atomically.  The logical
`sync` here has no filesystem effect; a physical adapter would additionally
have to refine the VFS durability contract. -/
def executeWrite (connection : WALConnection) (sql : String) :
    IO (Except String (List Core.Result)) := do
  connection.writerLock.lock
  try
    let database ← connection.snapshot
    match CoreSQL.execute { database := database } sql with
    | .error message => return .error message
    | .ok (next, results) =>
        connection.state.atomically do
          let wal ← get
          set (wal.commit next.database)
        return .ok results
  finally
    connection.writerLock.unlock

end WALConnection

end SQLeanite
