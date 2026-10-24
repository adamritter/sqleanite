namespace SQLeanite.SQLite.Limits

/-- The pinned SQLite build uses the default SQLITE_MAX_LENGTH. This is a
byte count, shared by TEXT/BLOB storage and newly produced scalar values. -/
abbrev maxLength : Nat := 1000000000

def check (payloadBytes : Nat) (allocationOverhead : Nat := 0) : Except String Unit :=
  if payloadBytes + allocationOverhead ≤ maxLength then .ok ()
  else .error "string or blob too big"

theorem check_success (payloadBytes overhead : Nat) :
    check payloadBytes overhead = .ok () ↔ payloadBytes + overhead ≤ maxLength := by
  simp [check]

theorem check_excess (payloadBytes overhead : Nat)
    (excess : maxLength < payloadBytes + overhead) :
    check payloadBytes overhead = .error "string or blob too big" := by
  simp [check, Nat.not_le_of_lt excess]

end SQLeanite.SQLite.Limits
