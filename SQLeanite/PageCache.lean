namespace SQLeanite
namespace PageCache

variable {Key Value : Type} [DecidableEq Key]

structure Entry (Key Value : Type) where
  key : Key
  value : Value
  deriving Repr

def keys (entries : List (Entry Key Value)) : List Key :=
  entries.map Entry.key

def lookup (key : Key) : List (Entry Key Value) → Option Value
  | [] => none
  | entry :: entries =>
      if entry.key = key then some entry.value else lookup key entries

def erase (key : Key) : List (Entry Key Value) → List (Entry Key Value)
  | [] => []
  | entry :: entries =>
      if entry.key = key then erase key entries else entry :: erase key entries

theorem keys_erase (key : Key) (entries : List (Entry Key Value)) :
    keys (erase key entries) = (keys entries).filter (fun candidate => candidate != key) := by
  induction entries with
  | nil => rfl
  | cons entry entries induction =>
      unfold erase
      split
      next equal =>
        rw [induction]
        simp [keys, equal]
      next different =>
        change entry.key :: keys (erase key entries) =
          (entry.key :: keys entries).filter (fun candidate => candidate != key)
        rw [induction]
        simp [different]

theorem mem_of_mem_erase (key : Key) {entry : Entry Key Value}
    {entries : List (Entry Key Value)} (member : entry ∈ erase key entries) :
    entry ∈ entries := by
  induction entries with
  | nil => simp [erase] at member
  | cons head rest induction =>
      unfold erase at member
      split at member
      · exact List.mem_cons_of_mem _ (induction member)
      · rcases List.mem_cons.mp member with equal | tail
        · exact List.mem_cons.mpr (.inl equal)
        · exact List.mem_cons_of_mem _ (induction tail)

theorem lookup_some_mem {key : Key} {value : Value}
    {entries : List (Entry Key Value)} (found : lookup key entries = some value) :
    ∃ entry ∈ entries, entry.key = key ∧ entry.value = value := by
  induction entries with
  | nil => simp [lookup] at found
  | cons entry entries induction =>
      simp only [lookup] at found
      split at found
      next equal =>
        injection found with valueEqual
        exact ⟨entry, by simp, equal, valueEqual⟩
      next different =>
        rcases induction found with ⟨witness, member, keyEqual, valueEqual⟩
        exact ⟨witness, by simp [member], keyEqual, valueEqual⟩

/-- A bounded read cache. Values are safe to return only under `Coherent`,
which relates every resident entry to an authoritative store. -/
structure ReadCache (Key Value : Type) [DecidableEq Key] where
  capacity : Nat
  entries : List (Entry Key Value)
  unique : (keys entries).Nodup
  bounded : entries.length ≤ capacity

def ReadCache.empty (capacity : Nat) : ReadCache Key Value :=
  ⟨capacity, [], by simp [keys], by simp⟩

def ReadCache.insert (cache : ReadCache Key Value) (key : Key) (value : Value) :
    ReadCache Key Value := by
  let updated := ⟨key, value⟩ :: erase key cache.entries
  have erasedUnique : (keys (erase key cache.entries)).Nodup := by
    rw [keys_erase]
    exact cache.unique.filter _
  have keyAbsent : key ∉ keys (erase key cache.entries) := by
    rw [keys_erase]
    simp
  have updatedUnique : (keys updated).Nodup := by
    simp only [updated, keys, List.map_cons]
    exact List.nodup_cons.mpr ⟨keyAbsent, erasedUnique⟩
  exact {
    capacity := cache.capacity
    entries := updated.take cache.capacity
    unique := by
      rw [keys, List.map_take]
      exact updatedUnique.take
    bounded := by
      exact Nat.le_trans (List.length_take_le _ _) (Nat.le_refl _) }

def ReadCache.read (cache : ReadCache Key Value) (key : Key) : Option Value :=
  lookup key cache.entries

def ReadCache.Coherent (cache : ReadCache Key Value)
    (store : Key → Option Value) : Prop :=
  ∀ entry ∈ cache.entries, store entry.key = some entry.value

theorem ReadCache.read_refines {cache : ReadCache Key Value}
    {store : Key → Option Value} (coherent : cache.Coherent store)
    {key : Key} {value : Value} (found : cache.read key = some value) :
    store key = some value := by
  rcases lookup_some_mem found with ⟨entry, member, keyEqual, valueEqual⟩
  simpa [keyEqual, valueEqual] using coherent entry member

theorem ReadCache.insert_coherent (cache : ReadCache Key Value)
    (store : Key → Option Value) (coherent : cache.Coherent store)
    (key : Key) (value : Value) (authoritative : store key = some value) :
    (cache.insert key value).Coherent store := by
  intro entry member
  unfold ReadCache.insert at member
  simp only at member
  have inUpdated : entry ∈ (⟨key, value⟩ :: erase key cache.entries) :=
    List.mem_of_mem_take member
  rcases List.mem_cons.mp inUpdated with equal | inErased
  · subst entry
    exact authoritative
  · apply coherent entry
    exact mem_of_mem_erase key inErased

theorem ReadCache.read_insert_same (cache : ReadCache Key Value)
    (key : Key) (value : Value) (positive : 0 < cache.capacity) :
    (cache.insert key value).read key = some value := by
  cases capacity : cache.capacity with
  | zero => omega
  | succ capacity =>
      simp [ReadCache.insert, ReadCache.read, lookup, capacity]

/-- Dirty writes are kept separately from the bounded read cache. This avoids
the classic unsound design where capacity eviction silently drops a dirty
page. Re-putting one key removes its older value, implementing write
absorption. -/
structure WriteBuffer (Key Value : Type) [DecidableEq Key] where
  entries : List (Entry Key Value)
  unique : (keys entries).Nodup

def WriteBuffer.empty : WriteBuffer Key Value := ⟨[], by simp [keys]⟩

def WriteBuffer.put (buffer : WriteBuffer Key Value) (key : Key) (value : Value) :
    WriteBuffer Key Value := by
  have erasedUnique : (keys (erase key buffer.entries)).Nodup := by
    rw [keys_erase]
    exact buffer.unique.filter _
  have keyAbsent : key ∉ keys (erase key buffer.entries) := by
    rw [keys_erase]
    simp
  exact ⟨⟨key, value⟩ :: erase key buffer.entries,
    List.nodup_cons.mpr ⟨keyAbsent, erasedUnique⟩⟩

def WriteBuffer.read (buffer : WriteBuffer Key Value) (key : Key) : Option Value :=
  lookup key buffer.entries

theorem WriteBuffer.read_put_same (buffer : WriteBuffer Key Value)
    (key : Key) (value : Value) :
    (buffer.put key value).read key = some value := by
  simp [WriteBuffer.put, WriteBuffer.read, lookup]

/-- Flushing returns every latest dirty page and an empty buffer. The caller's
VFS is responsible for applying and syncing the returned writes. -/
def WriteBuffer.flush (buffer : WriteBuffer Key Value) :
    List (Entry Key Value) × WriteBuffer Key Value :=
  (buffer.entries, .empty)

theorem WriteBuffer.flush_writes (buffer : WriteBuffer Key Value) :
    buffer.flush.1 = buffer.entries := rfl

theorem WriteBuffer.flush_empty (buffer : WriteBuffer Key Value) :
    buffer.flush.2.entries = [] := rfl

end PageCache
end SQLeanite
