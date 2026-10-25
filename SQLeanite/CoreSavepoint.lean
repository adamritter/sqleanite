import SQLeanite.CoreEngine

/-! Named transaction marks, kept newest first. ROLLBACK TO retains the named
mark. RELEASE discards it and its younger marks; only the mark that opened the
transaction can publish the complete transaction. -/
namespace SQLeanite.CoreSavepoint

def remaining (name : String) (marks : List Core.Savepoint) : List Core.Savepoint :=
  marks.dropWhile (fun mark => mark.name.toLower != name.toLower)

def push (state : Core.State) (name : String) : Core.State :=
  { state with
    transactionSnapshot := some (state.transactionSnapshot.getD state.database)
    savepoints := ({
      name := name
      snapshot := state.database
      startsTransaction := state.transactionSnapshot.isNone } : Core.Savepoint) :: state.savepoints }

def release (state : Core.State) (name : String) : Except String Core.State :=
  match remaining name state.savepoints with
  | [] => .error s!"no such savepoint: {name}"
  | mark :: older => .ok { state with
      transactionSnapshot := if mark.startsTransaction then none else state.transactionSnapshot
      savepoints := older }

def rollbackTo (state : Core.State) (name : String) : Except String Core.State :=
  match remaining name state.savepoints with
  | [] => .error s!"no such savepoint: {name}"
  | mark :: older => .ok { state with database := mark.snapshot, savepoints := mark :: older }

def releasesTransaction (state : Core.State) (name : String) : Bool :=
  ((remaining name state.savepoints).head?).any (·.startsTransaction)

@[simp] theorem remaining_top (name : String) (snapshot : Core.Database)
    (startsTransaction : Bool) (older : List Core.Savepoint) :
    remaining name ({ name, snapshot, startsTransaction } :: older) =
      { name, snapshot, startsTransaction } :: older := by
  simp [remaining]

theorem push_transaction (state : Core.State) (name : String) :
    (push state name).transactionSnapshot.isSome = true := by
  simp [push]

theorem release_push (state : Core.State) (name : String) :
    release (push state name) name = .ok state := by
  cases state with
  | mk database snapshot marks =>
      cases snapshot <;> simp [release, push]

theorem rollbackTo_push (state : Core.State) (name : String) :
    rollbackTo (push state name) name = .ok (push state name) := by
  simp [rollbackTo, push]

theorem release_database (state next : Core.State) (name : String)
    (success : release state name = .ok next) : next.database = state.database := by
  unfold release at success
  split at success
  · contradiction
  · cases success
    rfl

theorem rollbackTo_snapshot (state : Core.State) (name : String)
    (mark : Core.Savepoint) (older : List Core.Savepoint)
    (found : remaining name state.savepoints = mark :: older) :
    rollbackTo state name = .ok { state with database := mark.snapshot, savepoints := mark :: older } := by
  simp [rollbackTo, found]

theorem releasesTransaction_push (state : Core.State) (name : String) :
    releasesTransaction (push state name) name = state.transactionSnapshot.isNone := by
  simp [releasesTransaction, push]

end SQLeanite.CoreSavepoint
