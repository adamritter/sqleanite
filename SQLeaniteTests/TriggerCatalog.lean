import SQLeaniteTests.ExpectForeignKeyPragmas
import SQLeanite.CoreTriggerSQL

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectTriggerCatalog : IO Unit := do
  let first := "CREATE /*header*/ TRIGGER x AFTER UPDATE ON t BEGIN SELECT CASE WHEN 1 THEN ';' ELSE 'END' END;SELECT 'end;'; END;"
  let last := "SELECT 9;"
  unless SQLite.Script.split (first++last) == [first,last,""] do
    fail "trigger splitting lost a body semicolon or confused CASE/string END"
  let temporary := "CREATE TEMP TRIGGER x AFTER INSERT ON t BEGIN SELECT new.id; END;"
  unless SQLite.Script.split (temporary++last) == [temporary,last,""] do
    fail "completion grammar lost TEMP trigger boundaries"
  let (base,_) ← foreignStatement Core.State.empty "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);"
  let sql := "CREATE TRIGGER main.\"Odd.Name\" AFTER UPDATE OF n,v ON T FOR EACH ROW WHEN old.n<>new.n BEGIN SELECT ';',new.id; END;"
  let (created,_) ← foreignStatement base sql
  let some source := CoreTriggerSQL.find? created "odd.name" | fail "trigger source was not retained"
  unless source.owner == "T" && source.definition.table == "T" do
    fail "trigger catalog owner lost its actual source spelling"
  match source.definition.event with
  | .updateOf columns => unless columns == #["n","v"] do fail "UPDATE OF lost its actual column list"
  | _ => fail "UPDATE OF became an unrestricted UPDATE event"
  unless source.text == "CREATE TRIGGER \"Odd.Name\" AFTER UPDATE OF n,v ON T FOR EACH ROW WHEN old.n<>new.n BEGIN SELECT ';',new.id; END" do
    fail "trigger header normalization changed name/body source bytes"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok value => pure value | .error message => fail message
  let some (Statement.createTrigger name table event timing when_ body guard temp display original) := parsed.statements[0]?
    | fail "missing trigger syntax fixture"
  let forged := Statement.createTrigger name table (.updateOf #["v"]) timing when_ body guard temp display original
  if (CoreTokenGrammar.check parsed.tokens #[forged]).isOk then fail "independent grammar accepted a forged UPDATE OF list"
  let (begun,_) ← foreignStatement created "BEGIN;"
  let (dropped,_) ← foreignStatement begun "DROP TRIGGER main.\"Odd.Name\";"
  unless dropped.catalog.current.triggers.isEmpty do fail "DROP TRIGGER retained its program"
  let (restored,_) ← foreignStatement dropped "ROLLBACK;"
  unless restored.catalog.current.contents == created.catalog.current.contents do
    fail "rollback lost trigger source, identity, owner or schema cookie"
  let (same,_) ← foreignStatement created "CREATE TRIGGER IF NOT EXISTS \"Odd.Name\" BEFORE DELETE ON t BEGIN SELECT old.id; END;"
  unless same.catalog.current.contents == created.catalog.current.contents do fail "IF NOT EXISTS replaced a trigger declaration"
  let (removed,_) ← foreignStatement created "DROP TABLE t;"
  unless removed.catalog.current.triggers.isEmpty do fail "dropping a table retained its trigger"
  let header := CoreFile.databaseHeader ⟨0, by decide⟩
  let some initialImage := CoreCatalogImage.encode 0 base.database header {} [] [] (some base.catalog.current)
    | fail "could not encode the pre-trigger physical catalog"
  let some initialRecords := CoreSchemaRead.rowsFrom (CorePageSource.ofStorageImage (CoreCatalogImage.storage initialImage))
    | fail "could not read the pre-trigger physical catalog"
  let projected ← match CoreSchemaRead.currentRecords created initialRecords with
    | .ok value => pure value | .error message => fail message
  unless projected.length == initialRecords.length+1 do fail "pending trigger was not visible before publication"
  let some originalTable := initialRecords.find? (fun row => row.values[0]?.bind CoreViewSQL.text? == some "table")
    | fail "missing original physical table root"
  let some retainedTable := projected.find? (fun row => row.values[0]?.bind CoreViewSQL.text? == some "table")
    | fail "pending program metadata hid a real physical table"
  unless retainedTable.values[3]? == originalTable.values[3]? do fail "pending program metadata invented a table rootpage"
  let some image := CoreCatalogImage.encode 0 created.database header {} [] [] (some created.catalog.current)
    | fail "could not encode actual trigger catalog fixture"
  unless CoreCatalogImage.objectsMatch created.catalog.current image do
    fail "encoded trigger catalog did not satisfy independent physical checks"
  let some records := CoreSchemaRead.rowsFrom (CorePageSource.ofStorageImage (CoreCatalogImage.storage image))
    | fail "could not independently read actual trigger catalog records"
  let wrongOwner ← match SQLSurface.value (.text "other") with
    | .ok value => pure value | .error message => fail message
  let wrongRoot ← match SQLSurface.value (.integer 2) with
    | .ok value => pure value | .error message => fail message
  let wrongSource ← match SQLSurface.value (.text "CREATE TRIGGER different AFTER INSERT ON t BEGIN SELECT new.id; END") with
    | .ok value => pure value | .error message => fail message
  for (column,value) in [(2,wrongOwner),(3,wrongRoot),(4,wrongSource)] do
    let forged := records.map fun row =>
      if row.values[0]?.bind CoreViewSQL.text? == some "trigger" then
        { row with values := row.values.set column value }
      else row
    if CoreCatalogImage.objectRecordsMatch created.catalog.current forged then
      fail "physical trigger check accepted a changed owner, nonzero root or SQL source"
  let (_,cookie) ← foreignStatement created "PRAGMA main.schema_version;"
  let expected ← match SQLSurface.value (.integer created.catalog.current.schemaVersion) with
    | .ok value => pure value | .error message => fail message
  unless cookie.flatMap (·.rows) == [[expected]] do fail "schema_version did not read the actual connection cookie"

end SQLeanite.Tests
