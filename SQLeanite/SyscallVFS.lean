import SQLeanite.POSIXVFS

namespace SQLeanite
namespace SyscallVFS

/-!
# Concrete POSIX durability boundary

These are the only two durability calls the rollback adapter asks the host to
implement.  Their C bodies contain no database logic: open a named file and
`fdatasync` it, or open its parent directory and `fsync` it.  The conditional
refinement assumptions for these calls are stated in `POSIXVFS`.
-/

@[extern "sqleanite_fdatasync_path"]
opaque fdatasyncPath (path : @& String) : IO Unit

@[extern "sqleanite_fsync_parent_path"]
opaque fsyncParentPath (path : @& String) : IO Unit

@[extern "sqleanite_pread_bytes"]
opaque preadBytes (path : @& String) (offset : UInt64) (length : USize) :
  IO ByteArray

@[extern "sqleanite_pwrite_bytes"]
opaque pwriteBytes (path : @& String) (offset : UInt64)
    (bytes : @& ByteArray) : IO Unit

/-- One byte-exact positional transfer selected by the verified page planner.
The native VFS batch functions only iterate this array; page identity, order,
and contents remain Lean values. -/
structure PageTransfer where
  bytes : ByteArray
  offset : UInt64

@[extern "sqleanite_pwrite_pages"]
opaque pwritePages (path : @& String)
    (writes : @& Array PageTransfer) : IO Unit

@[extern "sqleanite_verify_pages"]
opaque verifyPages (path : @& String)
    (writes : @& Array PageTransfer) : IO Unit

@[extern "sqleanite_rename_path"]
opaque renamePath (source target : @& String) : IO Unit

@[extern "sqleanite_unlink_path"]
opaque unlinkPath (path : @& String) : IO Unit

/-- Explicit assumptions needed to interpret completed Linux/POSIX operations
as the abstract crash model.  There is one field per syscall class, so the TCB
cannot hide rename or directory-entry persistence inside a generic statement.
No theorem below claims that a particular kernel, filesystem, or device
satisfies these assumptions. -/
structure Contract (pageSize : Nat) where
  ConcreteState : Type
  view : ConcreteState → POSIXVFS.State pageSize
  step : ConcreteState → POSIXVFS.Request pageSize →
    POSIXVFS.Response pageSize → ConcreteState → Prop
  crash : ConcreteState → GrowableStorage.Image pageSize →
    Option (GrowableStorage.Journal pageSize) → Prop
  preadStepRefines : ∀ state pageId response next,
    step state (.readMain pageId) response next →
      view next = POSIXVFS.modelStep (view state) (.readMain pageId)
  preadValueRefines : ∀ state pageId page next,
    step state (.readMain pageId) (.page page) next →
      pageId < (GrowableStorage.applyWrites (view state).main.durable
        (view state).main.pending).pageCount ∧
      page = (GrowableStorage.applyWrites (view state).main.durable
        (view state).main.pending).read pageId
  pwriteRefines : ∀ state write response next,
    step state (.pwriteMain write) response next →
      view next = POSIXVFS.modelStep (view state) (.pwriteMain write)
  fdatasyncMainRefines : ∀ state response next,
    step state .fdatasyncMain response next →
      view next = POSIXVFS.modelStep (view state) .fdatasyncMain
  writeJournalTempRefines : ∀ state journal response next,
    step state (.writeJournalTemp journal) response next →
      view next = POSIXVFS.modelStep (view state) (.writeJournalTemp journal)
  fdatasyncJournalRefines : ∀ state response next,
    step state .fdatasyncJournalTemp response next →
      view next = POSIXVFS.modelStep (view state) .fdatasyncJournalTemp
  renameatRefines : ∀ state response next,
    step state .renameJournal response next →
      view next = POSIXVFS.modelStep (view state) .renameJournal
  unlinkatRefines : ∀ state response next,
    step state .unlinkJournal response next →
      view next = POSIXVFS.modelStep (view state) .unlinkJournal
  fsyncDirectoryRefines : ∀ state response next,
    step state .fsyncDirectory response next →
      view next = POSIXVFS.modelStep (view state) .fsyncDirectory
  crashRefines : ∀ state recoveredMain recoveredJournal,
    crash state recoveredMain recoveredJournal →
      Nonempty (GrowableStorage.JournaledCrashOutcome
        (view state).abstract recoveredMain recoveredJournal)

def Contract.toAbstract (contract : Contract pageSize) :
    POSIXVFS.Contract pageSize where
  ConcreteState := contract.ConcreteState
  view := contract.view
  step := contract.step
  crash := contract.crash
  stepRefines := by
    intro state request response next completed
    cases request with
    | readMain pageId => exact contract.preadStepRefines _ _ _ _ completed
    | pwriteMain write => exact contract.pwriteRefines _ _ _ _ completed
    | fdatasyncMain => exact contract.fdatasyncMainRefines _ _ _ completed
    | writeJournalTemp journal =>
        exact contract.writeJournalTempRefines _ _ _ _ completed
    | fdatasyncJournalTemp =>
        exact contract.fdatasyncJournalRefines _ _ _ completed
    | renameJournal => exact contract.renameatRefines _ _ _ completed
    | unlinkJournal => exact contract.unlinkatRefines _ _ _ completed
    | fsyncDirectory => exact contract.fsyncDirectoryRefines _ _ _ completed
  readMainRefines := by
    intro state pageId page next completed
    exact contract.preadValueRefines _ _ _ _ completed
  crashRefines := contract.crashRefines

theorem completedCommit_refines (contract : Contract pageSize)
    {initial final : contract.ConcreteState}
    (old : GrowableStorage.Image pageSize)
    (writes : List (GrowableStorage.PageWrite pageSize))
    (initialView : contract.view initial = POSIXVFS.State.initial old)
    (executed : POSIXVFS.Execution contract.toAbstract initial
      (POSIXVFS.commitPlan old writes) final) :
    (contract.view final).abstract =
      GrowableStorage.rollbackCommitState old writes .committed :=
  POSIXVFS.Execution.commit_refines old writes initialView executed

end SyscallVFS
end SQLeanite
