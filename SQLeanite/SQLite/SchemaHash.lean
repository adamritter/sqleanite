import SQLeanite.Syntax

/-! Iteration order of SQLite 3.53.4's schema hash on the pinned 64-bit build.
The default 1024-byte soft allocation limit permits 64 sixteen-byte buckets. -/
namespace SQLeanite.SQLite.SchemaHash

def nameHash (name : String) : Nat :=
  ((name.toUTF8.data.toList.takeWhile (· != 0)).foldl (fun (hash : UInt32) byte =>
    (hash + UInt32.ofNat (byte.toNat &&& 223)) * 2654435761) 0).toNat

def insert (buckets : Nat) (name : String) (names : List String) : List String :=
  if buckets == 0 then name :: names else
    match names.findIdx? (fun current => nameHash current % buckets == nameHash name % buckets) with
    | none => name :: names
    | some position => names.take position ++ name :: names.drop position

theorem insert_length (buckets : Nat) (name : String) (names : List String) :
    (insert buckets name names).length = names.length + 1 := by
  unfold insert
  split
  · simp
  · split
    · simp
    · next position _ =>
        have parts := congrArg List.length (List.take_append_drop position names)
        simp only [List.length_append] at parts
        simp only [List.length_append, List.length_cons]
        omega

structure State where
  buckets : Nat := 0
  count : Nat := 0
  names : List String := []
  /-- Persistent catalog order, separately retained from live hash order. -/
  creation : List String := []
  revision : Nat := 0

def add (state : State) (name : String) : State :=
  let count := state.count + 1
  let size := if count ≥ 5 && count > 2 * state.buckets then min (count * 3) 64 else state.buckets
  let ordered := if size == state.buckets then state.names else
    state.names.foldl (fun names name => insert size name names) []
  { buckets := size, count, names := insert size name ordered
    creation := state.creation ++ [name], revision := state.revision + 1 }

def build (names : List String) : State :=
  ("sqlite_master" :: names).foldl add {}

def order (names : List String) : List String := (build names).names

def remove (state : State) (name : String) : State :=
  { state with
    count := state.count - 1
    names := state.names.filter (· != name)
    creation := state.creation.filter (· != name)
    revision := state.revision + 1 }

/-- Schema invalidation reloads catalog entries, while ordinary removal keeps
its existing buckets. The catalog's built-in entry is inserted first. -/
def reload (state : State) : State :=
  { build (state.creation.filter (· != "sqlite_master")) with revision := state.revision + 1 }

def rollback (current snapshot : State) : State :=
  if current.revision == snapshot.revision then snapshot else reload snapshot

theorem rollback_unchanged (state : State) : rollback state state = state := by
  simp [rollback]


end SQLeanite.SQLite.SchemaHash
