import SQLeaniteTests.TriggerPrograms

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectTriggerConstraints : IO Unit := do
  let mut state := Core.State.empty
  for sql in [
      "CREATE TABLE p(id INTEGER PRIMARY KEY);",
      "INSERT INTO p VALUES(1);",
      "CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));",
      "PRAGMA foreign_keys=ON;",
      "CREATE TRIGGER repair AFTER INSERT ON c BEGIN INSERT INTO p VALUES(new.pid);END;"] do
    state := (← foreignStatement state sql).1
  let (next,_) ← foreignStatement state "INSERT INTO c VALUES(4,40);"
  unless next.foreignKeys && !next.schemaProgram && next.foreignWrites.isEmpty &&
      next.lastChanges == 1 && next.totalChanges == state.totalChanges+2 && next.lastInsertRowid == 4 do
    fail "statement-boundary FK repair lost connection state or leaked internal program/written-row state"
  let (_,parent) ← foreignStatement next "SELECT id FROM p WHERE id=40;"
  let forty ← match SQLSurface.value (.integer 40) with
    | .ok value => pure value | .error message => fail message
  unless parent.flatMap (·.rows) == [[forty]] do fail "AFTER body failed to repair its real parent relation"
  let (duplicate,_) ← foreignStatement next "CREATE TRIGGER duplicate_assignment AFTER UPDATE ON c BEGIN UPDATE p SET id=abs(-9223372036854775808),rowid=(SELECT p.id);END;"
  let (preserved,_) ← foreignStatement duplicate "UPDATE c SET pid=pid WHERE id=4;"
  unless preserved.foreignKeys && !preserved.schemaProgram && preserved.foreignWrites.isEmpty do
    fail "captured duplicate SET leaked its FK or schema-program context"
  let (unsafeState,_) ← foreignStatement preserved "CREATE TRIGGER unsafe_program AFTER DELETE ON c BEGIN SELECT * FROM pragma_foreign_key_check;END;"
  let parsed ← match CoreTokenGrammar.parseCertified "DELETE FROM c WHERE 0;" with
    | .ok value => pure value | .error message => fail message
  let some command := parsed.statements[0]? | fail "missing direct-only virtual-table fixture"
  match CoreDerivedSQL.executeStatement unsafeState command "DELETE FROM c WHERE 0;" with
  | .error message => unless message == "unsafe use of virtual table \"pragma_foreign_key_check\"" do fail message
  | .ok _ => fail "trigger preparation admitted a direct-only PRAGMA virtual table"

end SQLeanite.Tests
