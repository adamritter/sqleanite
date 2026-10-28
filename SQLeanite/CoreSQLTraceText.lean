import SQLeanite.CoreSQLTraceText.TraceCommand
import SQLeanite.CoreSQLTraceText.ExecuteTextCommittedLocalizedIndexedInlineTablesCrashAtomic

/-! Compatibility import for the responsibility modules above. -/

/-!
# Transactional SQL write traces

This layer extends persisted write commands with BEGIN and ROLLBACK.  They do
not themselves require a disk delta, but they cannot be erased: both change
the transaction snapshot that determines the meaning of later commands.
-/
