import SQLeanite.CoreSQLWriteText.OneResult
import SQLeanite.CoreSQLWriteText.ExecuteTextTraceRecoveryCrashTraceAtomic

/-! Compatibility import for the responsibility modules above. -/

/-!
# Supported SQL write text to durable Core commands

This module makes the write side of the text boundary explicit.  The relation
below is independent of execution success: its premises are parser and
translation equations plus the syntactic restrictions of the supported Core
surface.  The first version covers one persisted command per SQL statement;
multi-row INSERT and multi-statement transaction traces are composed later.
-/
