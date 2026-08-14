import SQLeanite.PhysicalJournalCodec
import SQLeanite.PhysicalFreelist
import SQLeanite.POSIXVFS
import SQLeanite.PhysicalJournalRecovery
import SQLeanite.SyscallVFS

namespace SQLeanite
namespace PhysicalFileAdapter

open PhysicalCodec

/-!
# Thin file adapter for the concrete MVP codec

The pure request plan is connected to `GrowableStorage.rollbackCommitState`.
The IO implementation writes the growable multi-page image and a page-level
undo journal. Its two POSIX durability calls remain an explicit, tiny TCB.
-/

abbrev Request := GrowableStorage.VFSRequest PhysicalCodec.pageSize

/-- The exact VFS request sequence for a successful growable rollback-journal
commit. Every target page is staged, making the plan independent of dirty-page
tracking while that optimization remains unverified. -/
def commitPlan (old new : PhysicalTableBTree.Tree) : List Request :=
  let writes := PhysicalMultiPageCodec.transactionWrites new
  [ .writeJournal (some (GrowableStorage.makeJournal
      (PhysicalMultiPageCodec.storageImage old) writes)),
    .syncJournal ] ++ writes.map GrowableStorage.VFSRequest.writeMain ++
      [.syncMain, .writeJournal none, .syncJournal]

def commitImagePlan (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (new : PhysicalFreelist.Layout) : List Request :=
  let writes := new.transactionWrites
  [ .writeJournal (some (GrowableStorage.makeJournal old writes)),
    .syncJournal ] ++ writes.map GrowableStorage.VFSRequest.writeMain ++
      [.syncMain, .writeJournal none, .syncJournal]

/-- Pure interpretation of requests that change modeled VFS state.  Reads are
irrelevant to the fixed commit plan and leave the state unchanged. -/
def modelStep (state : GrowableStorage.JournaledState PhysicalCodec.pageSize)
    (request : Request) : GrowableStorage.JournaledState PhysicalCodec.pageSize :=
  match request with
  | .readMain _ => state
  | .writeMain write => { state with main := state.main.write write }
  | .syncMain => { state with main := state.main.sync }
  | .writeJournal journal => { state with journal := state.journal.write journal }
  | .syncJournal => { state with journal := state.journal.sync }

def runPlan : GrowableStorage.JournaledState PhysicalCodec.pageSize → List Request →
    GrowableStorage.JournaledState PhysicalCodec.pageSize
  | state, [] => state
  | state, request :: requests => runPlan (modelStep state request) requests

theorem runPlan_writeMain_append
    (state : GrowableStorage.JournaledState PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (requests : List Request) :
    runPlan state
        (writes.map GrowableStorage.VFSRequest.writeMain ++ requests) =
      runPlan { state with main := state.main.writeAll writes } requests := by
  induction writes generalizing state with
  | nil => simp [runPlan, GrowableStorage.Cache.writeAll]
  | cons write writes induction =>
      simp only [List.map_cons, List.cons_append, runPlan, modelStep]
      rw [induction]
      congr 2
      simp [GrowableStorage.Cache.writeAll, GrowableStorage.Cache.write,
        List.append_assoc]

/-- The adapter plan is not merely a similar-looking sequence: in the pure
model it is exactly the verified committed checkpoint. -/
theorem run_commitPlan (old new : PhysicalTableBTree.Tree) :
    runPlan (GrowableStorage.JournaledState.initial
      (PhysicalMultiPageCodec.storageImage old))
      (commitPlan old new) =
    GrowableStorage.rollbackCommitState (PhysicalMultiPageCodec.storageImage old)
      (PhysicalMultiPageCodec.transactionWrites new) .committed := by
  unfold commitPlan
  simp only [List.cons_append, List.nil_append, runPlan, modelStep]
  rw [runPlan_writeMain_append]
  simp [runPlan, modelStep,
    GrowableStorage.rollbackCommitState,
    GrowableStorage.JournaledState.initial,
    GrowableStorage.JournaledState.writeJournal,
    GrowableStorage.JournaledState.syncJournal,
    GrowableStorage.JournaledState.stageMainWrites,
    GrowableStorage.JournaledState.syncMain,
    GrowableStorage.JournaledState.deleteJournal,
    GrowableStorage.Cache.writeAll, GrowableStorage.Cache.write]

theorem run_commitImagePlan (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (new : PhysicalFreelist.Layout) :
    runPlan (GrowableStorage.JournaledState.initial old)
      (commitImagePlan old new) =
    GrowableStorage.rollbackCommitState old new.transactionWrites .committed := by
  unfold commitImagePlan
  simp only [List.cons_append, List.nil_append, runPlan, modelStep]
  rw [runPlan_writeMain_append]
  simp [runPlan, modelStep,
    GrowableStorage.rollbackCommitState,
    GrowableStorage.JournaledState.initial,
    GrowableStorage.JournaledState.writeJournal,
    GrowableStorage.JournaledState.syncJournal,
    GrowableStorage.JournaledState.stageMainWrites,
    GrowableStorage.JournaledState.syncMain,
    GrowableStorage.JournaledState.deleteJournal,
    GrowableStorage.Cache.writeAll, GrowableStorage.Cache.write]

theorem commitImage_crash_atomic (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (new : PhysicalFreelist.Layout)
    (doesNotShrink : old.pageCount ≤ new.storageImage.pageCount)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState old new.transactionWrites phase)
      recoveredMain recoveredJournal) :
    (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal).Equiv old ∨
      (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal).Equiv
        new.storageImage := by
  rcases GrowableStorage.rollbackCommit_crash_atomic old new.transactionWrites
      phase recoveredMain recoveredJournal outcome with oldState | writtenState
  · exact .inl oldState
  · exact .inr (writtenState.trans
      (GrowableStorage.apply_replaceWrites_equiv old new.storageImage doesNotShrink))

structure Paths where
  main : System.FilePath
  journal : System.FilePath

def Paths.journalTemp (paths : Paths) : System.FilePath :=
  System.FilePath.mk (paths.journal.toString ++ ".tmp")

/-- The OS durability boundary. Tests may supply a different implementation;
the system implementation maps directly to the two calls named in the VFS
refinement assumptions. -/
structure SyncOps where
  syncFile : System.FilePath → IO Unit
  syncDeletion : System.FilePath → IO Unit

def SyncOps.system : SyncOps := {
  syncFile := fun path => SyscallVFS.fdatasyncPath path.toString
  syncDeletion := fun survivingPath =>
    SyscallVFS.fsyncParentPath survivingPath.toString
}

private def bytes (values : List UInt8) : ByteArray :=
  ByteArray.mk values.toArray

private def buildTree (database : PhysicalCodec.Database) : IO PhysicalTableBTree.Tree :=
  match PhysicalTableBTree.build database with
  | some tree => return tree
  | none => throw (IO.userError "MVP database does not fit the physical table B-tree")

def reopen (paths : Paths) : IO PhysicalCodec.Database := do
  let contents ← IO.FS.readBinFile paths.main
  match PhysicalFreelist.decodeFile contents.data.toList with
  | some database => return database
  | none => throw (IO.userError s!"invalid MVP SQLite image: {paths.main}")

/-- Create or replace the growable main file and clear a stale journal. -/
def create (syncOps : SyncOps) (paths : Paths)
    (database : PhysicalCodec.Database) : IO Unit := do
  let tree ← buildTree database
  if ← paths.journalTemp.pathExists then
    SyscallVFS.unlinkPath paths.journalTemp.toString
  if ← paths.journal.pathExists then
    SyscallVFS.unlinkPath paths.journal.toString
  IO.FS.writeBinFile paths.main (bytes (PhysicalMultiPageCodec.fileBytes tree))
  syncOps.syncFile paths.main
  syncOps.syncDeletion paths.main

/-- Recover an interrupted commit by restoring every page preimage and then
truncating to the original page count carried in the journal header. -/
def recover (syncOps : SyncOps) (paths : Paths) : IO PhysicalCodec.Database := do
  if ← paths.journalTemp.pathExists then
    SyscallVFS.unlinkPath paths.journalTemp.toString
    syncOps.syncDeletion paths.main
  if ← paths.journal.pathExists then
    let encoded ← IO.FS.readBinFile paths.journal
    let journal ← match PhysicalJournalCodec.decodeChecked encoded.data.toList with
      | some journal => pure journal
      | _ => throw (IO.userError "invalid MVP rollback journal")
    let current ← IO.FS.readBinFile paths.main
    let currentPageCount := current.size / PhysicalCodec.pageSize
    unless current.size = currentPageCount * PhysicalCodec.pageSize do
      throw (IO.userError "misaligned MVP main file during recovery")
    let recoveredMain ← match PhysicalJournalRecovery.decodeImage
        currentPageCount current.data.toList with
      | some image => pure image
      | none => throw (IO.userError "invalid paged MVP main file during recovery")
    let restored := PhysicalJournalRecovery.recoverBytes recoveredMain (some journal)
    IO.FS.writeBinFile paths.main (bytes restored)
    syncOps.syncFile paths.main
    SyscallVFS.unlinkPath paths.journal.toString
    syncOps.syncDeletion paths.main
  reopen paths

/-- Execute the page-level rollback protocol and reopen the committed image.
The returned trace is the pure request plan whose model equality is proved by
`run_commitPlan`. -/
def commit (syncOps : SyncOps) (paths : Paths) (new : PhysicalCodec.Database) :
    IO (PhysicalCodec.Database ×
      List (POSIXVFS.Request PhysicalCodec.pageSize)) := do
  let old ← recover syncOps paths
  let _oldTree ← buildTree old
  let newTree ← buildTree new
  let current ← IO.FS.readBinFile paths.main
  let oldImage ← match PhysicalFreelist.physicalImage? current.data.toList with
    | some image => pure image
    | none => throw (IO.userError "could not page the current MVP image")
  let targetPageCount := max oldImage.pageCount
    (PhysicalMultiPageCodec.filePageCount newTree)
  let layout ← match PhysicalFreelist.ofTreeTotal? newTree targetPageCount with
    | some layout => pure layout
    | none => throw (IO.userError "MVP freelist exceeds the verified single-trunk bound")
  let writes := layout.transactionWrites
  let journal := GrowableStorage.makeJournal oldImage writes
  let encodable ← match PhysicalJournalCodec.ofJournal? journal with
    | some value => pure value
    | none => throw (IO.userError "MVP rollback journal exceeds encoded bounds")
  IO.FS.writeBinFile paths.journalTemp
    (bytes (PhysicalJournalCodec.encodeChecked encodable))
  syncOps.syncFile paths.journalTemp
  SyscallVFS.renamePath paths.journalTemp.toString paths.journal.toString
  syncOps.syncDeletion paths.main
  IO.FS.writeBinFile paths.main (bytes layout.fileBytes)
  syncOps.syncFile paths.main
  SyscallVFS.unlinkPath paths.journal.toString
  syncOps.syncDeletion paths.main
  let reopened ← reopen paths
  return (reopened, POSIXVFS.commitPlan oldImage writes)

end PhysicalFileAdapter
end SQLeanite
