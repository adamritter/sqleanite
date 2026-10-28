import SQLeanite.CoreDecode.DecodeCanonicalTableStepEncoded
import SQLeaniteTests.ExpectSQLiteJsonBinaryEscapes

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectForeignKeyPragmas : IO Unit := do
  let (state, _) ← match CoreSourceSQL.execute Core.State.empty
      "CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(x REFERENCES p(id));INSERT INTO c VALUES(99);" with
    | .ok result => pure result | .error message => fail message
  let cases : List (String × List (List Value)) := [
    ("PRAGMA foreign_key_list(c);", [[.integer 0,.integer 0,.text "p",.text "x",.text "id",.text "NO ACTION",.text "NO ACTION",.text "NONE"]]),
    ("PRAGMA foreign_key_check(c);", [[.text "c",.integer 1,.text "p",.integer 0]]),
    ("SELECT rowid,parent,fkid FROM pragma_foreign_key_check('c');", [[.integer 1,.text "p",.integer 0]]),
    ("SELECT id,arg,schema FROM pragma_foreign_key_list('c');", [[.integer 0,.text "c",.null]])]
  for (sql, expected) in cases do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing foreign-key inspection statement"
    let (next, results) ← match CoreDerivedSQL.executeStatement state statement sql with
      | .ok result => pure result | .error message => fail message
    let expected ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result | .error message => fail message
    unless results.flatMap (·.rows) == expected do fail s!"wrong foreign-key inspection result: {sql}"
    unless next.database.contents == state.database.contents && next.lastInsertRowid == state.lastInsertRowid &&
        next.foreignKeys == state.foreignKeys do fail "foreign-key inspection changed connection state"

def foreignStatement (state : Core.State) (sql : String) : IO (Core.State × List Core.Result) := do
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing foreign-key statement"
  match CoreDerivedSQL.executeStatement state statement sql with
  | .ok result => pure result | .error message => fail message

def expectForeignKeyRename : IO Unit := do
  let (initial, _) ← match CoreSourceSQL.execute Core.State.empty
      "CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(x REFERENCES p(id));INSERT INTO c VALUES(1);" with
    | .ok result => pure result | .error message => fail message
  let (enabled, _) ← foreignStatement initial "PRAGMA foreign_keys=ON;"
  let (renamed, _) ← foreignStatement enabled "ALTER TABLE p RENAME TO \"new parent\";"
  let (state, _) ← foreignStatement renamed "ALTER TABLE \"new parent\" RENAME COLUMN id TO renamed;"
  unless state.foreignKeys && state.lastInsertRowid == initial.lastInsertRowid do
    fail "parent renaming changed connection registers"
  let some child := state.database.findTable? "c" | fail "renaming lost the child table"
  let keys ← match CoreForeignKeyData.keys child with
    | .ok keys => pure keys | .error message => fail message
  unless keys.map (·.2) == [{ table := "new parent", column := some "renamed" }] do
    fail "renaming lost the retained parent name or column"
  let some image := CoreFile.encode state.database | fail "renamed foreign-key encoding failed"
  let some database := CoreDecode.decode image.fileBytes | fail "renamed foreign-key decoding failed"
  let (_, results) ← foreignStatement { state with database } "PRAGMA foreign_key_check;"
  unless results.flatMap (·.rows) |>.isEmpty do fail "valid references broke after reopening renamed schema"
  let parsed ← match CoreTokenGrammar.parseCertified "INSERT INTO c VALUES(99);" with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing renamed-parent violation"
  match CoreDerivedSQL.executeStatement { state with database } statement "INSERT INTO c VALUES(99);" with
  | .ok _ => fail "renamed parent stopped enforcing its foreign key"
  | .error message => unless message == "FOREIGN KEY constraint failed" do fail message

def expectTableForeignKeys : IO Unit := do
  let (initial, _) ← match CoreSourceSQL.execute Core.State.empty
      "CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);" with
    | .ok result => pure result | .error message => fail message
  let sql := "CREATE TABLE c(x REFERENCES p(id),y,CONSTRAINT fk FOREIGN KEY(y) REFERENCES p(id));"
  let (created, _) ← match CoreSourceSQL.execute initial sql with
    | .ok result => pure result | .error message => fail message
  let (enabled, _) ← foreignStatement created "PRAGMA foreign_keys=ON;"
  let (inserted, _) ← foreignStatement enabled "INSERT INTO c VALUES(1,1);"
  let (state, _) ← foreignStatement inserted "ALTER TABLE c RENAME COLUMN y TO renamed;"
  let some image := CoreFile.encode state.database | fail "table foreign-key encoding failed"
  let some database := CoreDecode.decode image.fileBytes | fail "table foreign-key decoding failed"
  let some child := database.findTable? "c" | fail "table foreign-key child is missing"
  let keys ← match CoreForeignKeyData.keys child with
    | .ok keys => pure keys | .error message => fail message
  unless keys.map (·.1) == [0,1] do fail "column/table foreign-key declaration order changed"
  let parsedBad ← match CoreTokenGrammar.parseCertified "INSERT INTO c VALUES(1,99);" with
    | .ok result => pure result | .error message => fail message
  let some bad := parsedBad.statements[0]? | fail "missing table foreign-key violation"
  match CoreDerivedSQL.executeStatement { state with database } bad "INSERT INTO c VALUES(1,99);" with
  | .ok _ => fail "table FOREIGN KEY stopped enforcing after reopening"
  | .error message => unless message == "FOREIGN KEY constraint failed" do fail message
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok result => pure result | .error message => fail message
  let some (Statement.createTable name columns constraints guard) := parsed.statements[0]?
    | fail "missing table foreign-key declaration"
  let some constraint := constraints[0]? | fail "table foreign-key metadata was discarded"
  let forged := constraints.set! 0 { constraint with columns := #["x"] }
  if (CoreTokenGrammar.check parsed.tokens #[.createTable name columns forged guard]).isOk then
    fail "token replay accepted a changed FOREIGN KEY child target"

def expectStoredGeneratedColumns : IO Unit := do
  let sql := "CREATE TABLE g(a INT,b INT AS(c+1) STORED,c INT AS(a+1) STORED);"
  let (created, _) ← foreignStatement Core.State.empty sql
  let (state, result) ← foreignStatement created "INSERT INTO g(a) VALUES(2) RETURNING a,b,c;"
  let expected ← match [[Value.integer 2,.integer 4,.integer 3]].mapM (List.mapM SQLSurface.value) with
    | .ok result => pure result | .error message => fail message
  unless result.flatMap (·.rows) == expected do fail "generated dependency order was lost"
  let some table := state.database.findTable? "g" | fail "generated table is missing"
  let some source := table.catalogSource | fail "generated program was not retained"
  let program ← match source.compiledGeneratedColumns with
    | .ok result => pure result | .error message => fail message
  unless program.map (·.position) == [1,2] && program.map (·.dependencies) == [[2],[0]] do
    fail "generated program positions or dependencies were changed"
  let some image := CoreFile.encode state.database | fail "generated encoding failed"
  let some database := CoreDecode.decode image.fileBytes | fail "generated decoding failed"
  let (reopened, updated) ← foreignStatement { state with database } "UPDATE g SET a=5 RETURNING a,b,c;"
  let updatedExpected ← match [[Value.integer 5,.integer 7,.integer 6]].mapM (List.mapM SQLSurface.value) with
    | .ok result => pure result | .error message => fail message
  unless updated.flatMap (·.rows) == updatedExpected do fail "reopened generated UPDATE was not recomputed"
  let (_, metadata) ← foreignStatement reopened "SELECT cid,name,hidden FROM pragma_table_xinfo('g');"
  let metadataExpected ← match [[Value.integer 0,.text "a",.integer 0],
      [.integer 1,.text "b",.integer 3],[.integer 2,.text "c",.integer 3]].mapM (List.mapM SQLSurface.value) with
    | .ok result => pure result | .error message => fail message
  unless metadata.flatMap (·.rows) == metadataExpected do fail "STORED xinfo metadata was lost"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok result => pure result | .error message => fail message
  let some (Statement.createTable name columns constraints guard) := parsed.statements[0]?
    | fail "generated declaration was discarded"
  let changed := columns.map fun column => { column with generatedStored := false }
  if (CoreTokenGrammar.check parsed.tokens #[.createTable name changed constraints guard]).isOk then
    fail "token replay accepted forged generated storage semantics"
  let (loop, _) ← foreignStatement Core.State.empty "CREATE TABLE loop(a,b AS(b+1) STORED);"
  let input := "INSERT INTO loop(a) SELECT 1 WHERE 0;"
  let parsedInput ← match CoreTokenGrammar.parseCertified input with
    | .ok result => pure result | .error message => fail message
  let some statement := parsedInput.statements[0]? | fail "missing generated loop input"
  match CoreDerivedSQL.executeStatement loop statement input with
  | .ok _ => fail "empty INSERT did not validate its generated cycle"
  | .error message => unless message == "generated column loop on \"b\"" do fail message

def expectGeneratedColumnDDL : IO Unit := do
  let (empty, _) ← foreignStatement Core.State.empty "CREATE TABLE g(a);"
  let (state, _) ← foreignStatement empty "INSERT INTO g VALUES(1);"
  for (sql,expected) in [
      ("ALTER TABLE g ADD b AS(a+1) STORED NOT NULL;", "cannot add a STORED column"),
      ("ALTER TABLE g ADD b AS(a+1) STORED UNIQUE;", "Cannot add a UNIQUE column"),
      ("ALTER TABLE g ADD b AS(a+1) STORED PRIMARY KEY;", "generated columns cannot be part of the PRIMARY KEY")] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok result => pure result | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing generated ALTER input"
    match CoreDerivedSQL.executeStatement state statement sql with
    | .ok _ => fail "invalid generated ALTER was accepted"
    | .error message => unless message == expected do fail message
  let (onlyOrdinary, _) ← foreignStatement Core.State.empty "CREATE TABLE remaining(a,b AS(1) STORED);"
  let sql := "ALTER TABLE remaining DROP a;"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok result => pure result | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing generated DROP input"
  match CoreDerivedSQL.executeStatement onlyOrdinary statement sql with
  | .ok _ => fail "last ordinary column was dropped from a generated table"
  | .error message =>
      unless message == "error in table remaining after drop column: must have at least one non-generated column" do fail message

def expectGeneratedInsertTargets : IO Unit := do
  let (state, _) ← foreignStatement Core.State.empty "CREATE TABLE g(a,b AS(a+1) STORED);"
  for (sql,expected) in [
      ("INSERT INTO g SELECT 1,2;", "table g has 1 columns but 2 values were supplied"),
      ("INSERT INTO g(a) SELECT 1,2;", "2 values for 1 columns"),
      ("INSERT INTO g SELECT * FROM (VALUES(1,2));", "table g has 1 columns but 2 values were supplied"),
      ("INSERT INTO g VALUES(absent(1),2);", "no such function: absent"),
      ("INSERT INTO g VALUES(1),(2,3);", "all VALUES must have the same number of terms")] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok result => pure result | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing generated INSERT input"
    match CoreDerivedSQL.executeStatement state statement sql with
    | .ok _ => fail "invalid generated INSERT arity was accepted"
    | .error message => unless message == expected do fail message
  let parsed ← match CoreTokenGrammar.parseCertified "INSERT INTO g SELECT 1;" with
    | .ok result => pure result | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing implicit INSERT"
  let preserved ← match CoreGeneratedSQL.statement state statement with
    | .ok result => pure result | .error message => fail message
  match preserved with
  | .insertSelect _ columns .. => unless columns.isNone do fail "physical targets erased the source's omitted list"
  | _ => fail "implicit INSERT changed its statement form"

def expectDeclaredCollations : IO Unit := do
  let sql := "CREATE TABLE g(v TEXT COLLATE NOCASE,w TEXT);"
  let (created, _) ← foreignStatement Core.State.empty sql
  let (state, _) ← foreignStatement created "INSERT INTO g VALUES('a','A'),('A','a');"
  let some table := state.database.findTable? "g" | fail "declared-collation table is missing"
  let some source := table.catalogSource | fail "declared-collation source was lost"
  let declarations ← match source.compiledCollations with
    | .ok result => pure result | .error message => fail message
  unless declarations == [("v","nocase")] do fail "declared column program was not retained"
  for (query,count) in [
      ("SELECT count(*) FROM g WHERE v='a';", 2),
      ("SELECT count(*) FROM g WHERE w=v;", 0),
      ("SELECT count(*) FROM g WHERE v=w;", 2),
      ("SELECT count(*) FROM g WHERE v='a' COLLATE BINARY;", 1)] do
    let (_, result) ← foreignStatement state query
    let expected ← match SQLSurface.value (.integer count) with
      | .ok value => pure value | .error message => fail message
    unless result.flatMap (·.rows) == [[expected]] do fail s!"implicit/explicit collation priority changed: {query}"
  let some image := CoreFile.encode state.database | fail "declared-collation encoding failed"
  let some database := CoreDecode.decode image.fileBytes | fail "declared-collation decoding failed"
  let (_, result) ← foreignStatement { state with database } "SELECT count(DISTINCT v) FROM g;"
  let one ← match SQLSurface.value (.integer 1) with
    | .ok value => pure value | .error message => fail message
  unless result.flatMap (·.rows) == [[one]] do fail "declared collation was lost after reopening"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok result => pure result | .error message => fail message
  let some (Statement.createTable name columns constraints guard) := parsed.statements[0]?
    | fail "declared collation was discarded"
  let forged := columns.map fun column => { column with collation := "binary" }
  if (CoreTokenGrammar.check parsed.tokens #[.createTable name forged constraints guard]).isOk then
    fail "independent replay accepted a changed declared collation"
  if (CoreTokenGrammar.parseCertified "SELECT __sqlean_declared_collation('a','nocase');").isOk then
    fail "internal declared-collation annotation became a SQL function"

def expectDeclaredMembership : IO Unit := do
  let (created, _) ← foreignStatement Core.State.empty "CREATE TABLE g(v TEXT COLLATE NOCASE,w TEXT);"
  let (state, _) ← foreignStatement created "INSERT INTO g VALUES('a','A'),('A','a');"
  for (sql,values) in [
      ("SELECT 'A' IN (SELECT v FROM g WHERE rowid=1);", [1]),
      ("SELECT v IN (SELECT w FROM g WHERE rowid=1) FROM g ORDER BY rowid;", [1,1]),
      ("SELECT w IN (SELECT v FROM g WHERE rowid=1) FROM g ORDER BY rowid;", [0,1]),
      ("SELECT w IN (SELECT v COLLATE NOCASE FROM g WHERE rowid=1) FROM g ORDER BY rowid;", [1,1]),
      ("SELECT v IN (SELECT w COLLATE BINARY FROM g WHERE rowid=1) FROM g ORDER BY rowid;", [0,1]),
      ("SELECT (SELECT v FROM g WHERE rowid=1)='A';", [0]),
      ("SELECT (SELECT v COLLATE NOCASE FROM g WHERE rowid=1)='A';", [0])] do
    let (_, result) ← foreignStatement state sql
    let expected ← match values.mapM (fun value => do return [← SQLSurface.value (.integer value)]) with
      | .ok result => pure result | .error message => fail message
    unless result.flatMap (·.rows) == expected do
      fail s!"IN declaration/explicit priority or scalar isolation changed: {sql}"



def expectUTF16Predicates : IO Unit := do
  let (base,_) ← foreignStatement Core.State.empty "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);"
  let some stored := base.database.findTable? "t" | fail "missing native predicate schema"
  let one ← match SQLSurface.value (.integer 1) with
    | .ok value => pure value | .error message => fail message
  let .integer rowid := one | fail "native predicate rowid was not INTEGER"
  for encoding in [2,3] do
    for odd in [false,true] do
      let raw : Array UInt8 := (if encoding == 2 then #[0,216,65,0] else #[216,0,0,65]) ++ (if odd then #[65] else #[])
      let nativeHex := (if encoding == 2 then "00D84100" else "D8000041") ++ (if odd then "41" else "")
      let canonicalHex := if encoding == 2 then "00D841DC" else "D800DC41"
      if bound : raw.toList.length < PhysicalCodec.textByteLimit then
        let physical := [FileFormat.RecordField.null,PhysicalCodec.Text.recordField ⟨raw.toList,bound⟩]
        let some fields := CoreTextEncoding.fields encoding physical | fail "native predicate field decode failed"
        let some row := CoreRecord.decodeRowFields stored.schema rowid fields | fail "native predicate row decode failed"
        let table ← match Core.Table.rebuild stored.schema [] [row] stored.catalogSource with
          | .ok value => pure value | .error message => fail message
        let database ← match Core.Database.rebuild [table] with
          | .ok value => pure value | .error message => fail message
        let state := { base with database, catalog := { base.catalog with
          current := { base.catalog.current with textEncoding := encoding }
          storedTexts := CoreTextEncoding.origins encoding stored.schema row physical } }
        let cases : List (String × List (List Value)) := [
          (s!"SELECT CASE v WHEN CAST(X'{canonicalHex}' AS TEXT) THEN 1 ELSE 0 END FROM t;", [[.integer 0]]),
          (s!"SELECT v BETWEEN CAST(X'{canonicalHex}' AS TEXT) AND CAST(X'{canonicalHex}' AS TEXT) FROM t;", [[.integer 0]]),
          (s!"SELECT id FROM t WHERE v BETWEEN CAST(X'{canonicalHex}' AS TEXT) AND CAST(X'{canonicalHex}' AS TEXT);", []),
          (s!"SELECT v IN(CAST(X'{canonicalHex}' AS TEXT),'x','y') FROM t;", [[.integer 0]]),
          (s!"SELECT v IN(SELECT CAST(X'{canonicalHex}' AS TEXT)) FROM t;", [[.integer 0]]),
          (s!"SELECT count(*) FILTER(WHERE v=CAST(X'{canonicalHex}' AS TEXT)) FROM t;", [[.integer 0]]),
          (s!"SELECT count(*) FROM t HAVING min(v)=CAST(X'{canonicalHex}' AS TEXT);", []),
          ("SELECT hex((SELECT a.v)),(SELECT hex(a.v)) FROM t a;", [[.text nativeHex,.text nativeHex]]),
          ("SELECT NULL IN(SELECT v FROM t WHERE 0),v IN(SELECT v FROM t WHERE 0) FROM t;", [[.integer 0,.integer 0]]),
          ("SELECT id FROM t WHERE v BETWEEN CAST(X'FFFF' AS TEXT) AND abs(-9223372036854775808);", [])]
        for (sql,expected) in cases do
          let (_,results) ← foreignStatement state sql
          let expected ← expected.mapM (·.mapM fun value => match SQLSurface.value value with
            | .ok value => pure value | .error message => fail message)
          unless results.flatMap (·.rows) == expected do fail s!"native predicate or capture changed: {sql}"
        let sql := "SELECT v BETWEEN CAST(X'FFFF' AS TEXT) AND abs(-9223372036854775808) FROM t;"
        let parsed ← match CoreTokenGrammar.parseCertified sql with
          | .ok value => pure value | .error message => fail message
        let some statement := parsed.statements[0]? | fail "missing eager BETWEEN fixture"
        match CoreDerivedSQL.executeStatement state statement sql with
        | .error message => unless message == "integer overflow" do fail message
        | .ok _ => fail "scalar BETWEEN skipped a required failing upper operand"
      else fail "small native predicate fixture exceeded text bound"
  if (CoreTokenGrammar.parseCertified "SELECT __sqlean_encoded('stored',2,X'00D841');").isOk then
    fail "compiler-owned captured-byte annotation became public SQL"

def expectPersistentViews : IO Unit := do
  let (created,_) ← foreignStatement Core.State.empty "CREATE TABLE t(id INTEGER PRIMARY KEY,v VARCHAR(20),n INTEGER);"
  let (base,_) ← foreignStatement created "INSERT INTO t VALUES(1,'a',2),(2,'b',4);"
  let (viewState,_) ← foreignStatement base "CREATE VIEW IF NOT EXISTS q AS SELECT id,v,n FROM t;"
  let some view := CoreViewSQL.find? viewState "q" | fail "VIEW was not retained"
  unless view.text == "CREATE VIEW q AS SELECT id,v,n FROM t" do fail "VIEW normalization changed its SQL"
  match CoreCatalogData.parseView view.text with
  | none => fail "VIEW source did not retain its concrete grammar certificate"
  | some parsed => unless parsed.name == "q" do fail "VIEW declaration identity changed"
  let cases : List (String × List (List Value)) := [
    ("SELECT id,n FROM q ORDER BY id;", [[.integer 1,.integer 2],[.integer 2,.integer 4]]),
    ("WITH t AS (SELECT 99 AS id,'wrong' AS v,0 AS n) SELECT id,n FROM q ORDER BY id;", [[.integer 1,.integer 2],[.integer 2,.integer 4]]),
    ("SELECT t.id,(SELECT n FROM q WHERE q.id=t.id) FROM t ORDER BY id;", [[.integer 1,.integer 2],[.integer 2,.integer 4]]),
    ("SELECT name,type FROM pragma_table_info('q') ORDER BY cid;", [[.text "id",.text "INTEGER"],[.text "v",.text "VARCHAR(20)"],[.text "n",.text "INTEGER"]])]
  for (sql,expected) in cases do
    let (next,results) ← foreignStatement viewState sql
    let values ← expected.mapM (·.mapM fun value => match SQLSurface.value value with
      | .ok value => pure value | .error message => fail message)
    unless results.flatMap (·.rows) == values do fail s!"VIEW read or declaration changed: {sql}"
    unless CoreFileEngine.databaseContents next.database == CoreFileEngine.databaseContents viewState.database &&
        next.catalog.current.contents == viewState.catalog.current.contents && next.lastInsertRowid == viewState.lastInsertRowid do
      fail "private VIEW preparation escaped into the connection"
  for (sql,expected) in [
      ("INSERT INTO q VALUES(3,'c',6);", "cannot modify q because it is a view"),
      ("DROP TABLE q;", "use DROP VIEW to delete view q"),
      ("CREATE INDEX i ON q(n);", "views may not be indexed"),
      ("SELECT rowid FROM q;", "no such column: rowid")] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing VIEW diagnostic fixture"
    match CoreDerivedSQL.executeStatement viewState statement sql with
    | .ok _ => fail s!"VIEW error was not raised: {sql}"
    | .error message => unless message == expected do fail s!"VIEW diagnostic changed: {message}"
  let (withState,_) ← foreignStatement base "CREATE VIEW w AS WITH c AS (SELECT id,n FROM t) SELECT * FROM c;"
  let (_,withRows) ← foreignStatement withState "SELECT count(*) FROM w;"
  unless (withRows.flatMap (·.rows)).length == 1 do fail "VIEW WITH body did not execute"
  let (cycle,_) ← foreignStatement base "CREATE VIEW cycle AS SELECT * FROM cycle;"
  let parsed ← match CoreTokenGrammar.parseCertified "SELECT * FROM cycle;" with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing circular VIEW fixture"
  match CoreDerivedSQL.executeStatement cycle statement "SELECT * FROM cycle;" with
  | .error message => unless message == "view cycle is circularly defined" do fail message
  | .ok _ => fail "circular VIEW was evaluated"
  let (begun,_) ← foreignStatement viewState "BEGIN;"
  let (dropped,_) ← foreignStatement begun "DROP VIEW q;"
  let (restored,_) ← foreignStatement dropped "ROLLBACK;"
  unless restored.catalog.current.contents == viewState.catalog.current.contents do
    fail "rollback did not restore VIEW source, schema cookie and catalog rowids"
  let (renamed,_) ← foreignStatement viewState "ALTER TABLE t RENAME TO renamed;"
  let some renamedView := CoreViewSQL.find? renamed "q" | fail "renamed VIEW source disappeared"
  unless renamedView.text == "CREATE VIEW q AS SELECT id,v,n FROM \"renamed\"" do fail "ALTER did not retain renamed VIEW source"
  let (_,renamedRows) ← foreignStatement renamed "SELECT id,n FROM q ORDER BY id;"
  unless (renamedRows.flatMap (·.rows)).length == 2 do fail "renamed VIEW no longer reads base rows"
  let (roles,_) ← foreignStatement base "CREATE VIEW roles AS SELECT n AS n,'n' AS literal FROM t /* n remains */ ORDER BY n;"
  let (roles,_) ← foreignStatement roles "ALTER TABLE t RENAME COLUMN n TO amount;"
  let some source := CoreViewSQL.find? roles "roles" | fail "column rename lost VIEW"
  unless source.text == "CREATE VIEW roles AS SELECT amount AS n,'n' AS literal FROM t /* n remains */ ORDER BY n" do
    fail "ALTER renamed a literal, alias, comment or ORDER BY alias"
  let old : GrowableStorage.Image PhysicalCodec.pageSize := {
    pageCount := 0, read := fun _ => Storage.Page.zero PhysicalCodec.pageSize }
  let some image := CoreCatalogImage.encode 0 viewState.database (CoreFile.databaseHeader ⟨0, by decide⟩) {} [] [] (some viewState.catalog.current)
    | fail "VIEW image was not encoded"
  let some checked := CoreCatalogImage.check old viewState.database image | fail "VIEW image failed table component checks"
  let some attached := CoreCatalogImage.attachObjects checked viewState.catalog.current | fail "VIEW object check rejected its encoded bytes"
  unless attached.objectsEvidence.isSome && checked.catalog.any (fun entry => entry.kind == "view" &&
      entry.name == "q" && entry.rootPage == 0 && entry.sql == some view.text) do
    fail "VIEW root-zero catalog record or independent certificate is missing"
  let wrongCookie := { viewState.catalog.current with schemaVersion := viewState.catalog.current.schemaVersion + 1 }
  if (CoreCatalogImage.attachObjects checked wrongCookie).isSome then fail "object check accepted an unrelated schema cookie"
  let different ← match CoreCatalogData.view "CREATE VIEW q AS SELECT 99" with
    | .ok view => pure view | .error message => fail message
  let wrongSource := { viewState.catalog.current with views := [different] }
  if (CoreCatalogImage.attachObjects checked wrongSource).isSome then fail "object check accepted unrelated VIEW SQL"
  let parsed ← match CoreTokenGrammar.parseCertified "CREATE VIEW q AS WITH c AS (SELECT 1 AS x) SELECT x FROM c;" with
    | .ok parsed => pure parsed | .error message => fail message
  let some (Statement.createView name aliases query guard temporary text) := parsed.statements[0]?
    | fail "missing WITH VIEW syntax"
  let forged := { query with columns := #[{ expr := .literal (.integer 2) }] }
  match CoreTokenGrammar.check parsed.tokens #[.createView name aliases forged guard temporary text] with
  | .ok _ => fail "independent VIEW grammar accepted a changed WITH projection"
  | .error _ => pure ()

def expectDerivedCollations : IO Unit := do
  let (created, _) ← foreignStatement Core.State.empty "CREATE TABLE g(v TEXT COLLATE NOCASE,w TEXT);"
  let (state, _) ← foreignStatement created "INSERT INTO g VALUES('a','A'),('A','a');"
  let parsed ← match CoreTokenGrammar.parseCertified "SELECT v FROM g;" with
    | .ok parsed => pure parsed | .error message => fail message
  let query ← match parsed.statements.toList with
    | [.select query] => pure query | _ => fail "derived metadata fixture did not parse"
  let (privateState, name) ← match CoreDerivedSQL.materialize state query #[] with
    | .ok result => pure result | .error message => fail message
  let some table := privateState.database.findTable? name | fail "private source table is missing"
  let some source := table.catalogSource | fail "private collation source was not retained"
  let declarations ← match source.compiledCollations with
    | .ok declarations => pure declarations | .error message => fail message
  unless declarations == [("v","nocase")] do
    fail "derived result declarations do not match the checked private catalog"
  unless privateState.lastInsertRowid == state.lastInsertRowid do
    fail "private collation source changed last_insert_rowid"
  let cases : List (String × List (List Value)) := [
    ("SELECT count(*) FROM (SELECT v FROM g) AS d WHERE v='A';", [[.integer 2]]),
    ("SELECT count(*) FROM (SELECT v FROM g) AS d JOIN g AS b ON d.v=b.w;", [[.integer 4]]),
    ("SELECT count(*) FROM (SELECT v FROM g) AS d JOIN g AS b ON b.w=d.v;", [[.integer 2]]),
    ("SELECT 'A' IN (SELECT v FROM (SELECT v FROM g) AS d);", [[.integer 1]]),
    ("SELECT (SELECT v FROM (SELECT v FROM g) AS d LIMIT 1)='A';", [[.integer 0]]),
    ("SELECT rowid,(SELECT x FROM (SELECT g.v AS x) AS d)='A' FROM g ORDER BY rowid;", [[.integer 1,.integer 0],[.integer 2,.integer 1]]),
    ("SELECT CASE WHEN 0 THEN (SELECT x FROM (SELECT abs(-9223372036854775808) AS x) AS d) ELSE 17 END;", [[.integer 17]]),
    ("WITH q AS (SELECT v FROM g), r AS (SELECT * FROM q) SELECT count(*) FROM r WHERE v='A';", [[.integer 2]]),
    ("WITH q AS (SELECT abs(-9223372036854775808)), r AS (SELECT 17 AS x) SELECT x FROM r;", [[.integer 17]]),
    ("WITH RECURSIVE q(x) AS (SELECT 'a' COLLATE NOCASE UNION SELECT 'A' FROM q) SELECT count(*) FROM q;", [[.integer 1]]),
    ("WITH RECURSIVE q(x) AS (SELECT 'a' UNION SELECT 'A' COLLATE NOCASE FROM q) SELECT x,x='A' FROM q;", [[.text "a",.integer 0]])]
  for (sql,expected) in cases do
    let (next, result) ← foreignStatement state sql
    let expected ← expected.mapM (·.mapM fun value => match SQLSurface.value value with
      | .ok value => pure value | .error message => fail message)
    unless result.flatMap (·.rows) == expected do fail s!"derived scope or comparison metadata changed: {sql}"
    unless next.database.tables.length == state.database.tables.length do fail "a private derived source escaped a read"
  for (sql,expected) in [
      ("WITH RECURSIVE q(x) AS (SELECT 1 WHERE 0 UNION ALL SELECT absent(x) FROM q) SELECT * FROM q;", "no such function: absent"),
      ("WITH RECURSIVE q(x) AS (SELECT 1 WHERE 0 UNION ALL SELECT missing FROM q) SELECT * FROM q;", "no such column: missing"),
      ("WITH RECURSIVE q(x) AS (SELECT abs(-9223372036854775808) UNION ALL SELECT absent(x) FROM q) SELECT * FROM q;", "no such function: absent")] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed | .error message => fail message
    let some statement := parsed.statements[0]? | fail "recursive validation fixture is empty"
    match CoreDerivedSQL.executeStatement state statement sql with
    | .error message => unless message == expected do fail s!"recursive prepare diagnostic changed: {message}"
    | .ok _ => fail "an empty recursive seed skipped statement preparation"
  let (ctas, _) ← foreignStatement state "CREATE TABLE c AS SELECT v FROM (SELECT v FROM g) AS d;"
  let some stored := ctas.database.findTable? "c" | fail "derived CTAS destination is missing"
  unless !CoreDeclaredCollationSQL.tableUses stored && ctas.database.tables.length == 2 do
    fail "CTAS retained a private declaration or source table"
  let (_, result) ← foreignStatement ctas "SELECT count(*) FROM c WHERE v='A';"
  let expected ← match SQLSurface.value (.integer 1) with
    | .ok value => pure value | .error message => fail message
  unless result.flatMap (·.rows) == [[expected]] do fail "public CTAS did not reset output collation to BINARY"

def expectDeclaredCompounds : IO Unit := do
  let (created, _) ← foreignStatement Core.State.empty "CREATE TABLE g(v TEXT COLLATE NOCASE);"
  let (state, _) ← foreignStatement created "INSERT INTO g VALUES('a'),('A');"
  let (_, combined) ← foreignStatement state "SELECT v FROM g UNION SELECT 'A';"
  unless (combined.flatMap (·.rows)).length == 1 do fail "compound UNION ignored a declared result collation"
  let (_, removed) ← foreignStatement state "SELECT v FROM g EXCEPT SELECT 'A';"
  unless (removed.flatMap (·.rows)).isEmpty do fail "compound EXCEPT ignored a declared result collation"
  for (sql,value) in [
      ("SELECT 'A' IN (SELECT v FROM g WHERE rowid=1 UNION ALL SELECT NULL);", Value.null),
      ("SELECT 'A' IN (SELECT NULL UNION ALL SELECT v FROM g WHERE rowid=1);", .integer 1),
      ("SELECT 'A' IN (VALUES('a' COLLATE NOCASE),(NULL));", .integer 1),
      ("SELECT 'A' IN (VALUES(NULL),('a' COLLATE NOCASE));", .null)] do
    let (_, result) ← foreignStatement state sql
    let expected ← match SQLSurface.value value with
      | .ok value => pure value | .error message => fail message
    unless result.flatMap (·.rows) == [[expected]] do
      fail s!"compound/VALUES IN comparison selected the wrong operand metadata: {sql}"

def expectStrictTables : IO Unit := do
  let sql := "CREATE TABLE t(id INTEGER PRIMARY KEY,n INT,a ANY) STRICT;"
  let (created, _) ← match CoreSourceSQL.execute Core.State.empty sql with
    | .ok result => pure result | .error message => fail message
  let (state, _) ← foreignStatement created "INSERT INTO t VALUES(1,'003','003');"
  let some table := state.database.findTable? "t" | fail "STRICT table is missing"
  let some source := table.catalogSource | fail "STRICT type program was not retained"
  let program ← match source.compiledStrictColumns with
    | .ok result => pure result | .error message => fail message
  unless program == some [("id","INTEGER"),("n","INT"),("a","ANY")] do
    fail "STRICT declared types were not preserved"
  let (_, metadata) ← foreignStatement state "SELECT strict FROM pragma_table_list('t');"
  let flag ← match SQLSurface.value (.integer 1) with
    | .ok result => pure result | .error message => fail message
  unless metadata.flatMap (·.rows) == [[flag]] do fail "STRICT table_list flag was lost"
  let (_, result) ← foreignStatement state "SELECT n,a,typeof(n),typeof(a) FROM t;"
  let expected ← match [[Value.integer 3,.text "003",.text "integer",.text "text"]].mapM (List.mapM SQLSurface.value) with
    | .ok result => pure result | .error message => fail message
  unless result.flatMap (·.rows) == expected do fail "STRICT ANY applied ordinary numeric affinity"
  let some image := CoreFile.encode state.database | fail "STRICT encoding failed"
  let some database := CoreDecode.decode image.fileBytes | fail "STRICT decoding failed"
  match CoreSourceSQL.execute { state with database } "INSERT OR IGNORE INTO t VALUES(2,'bad','003');" with
  | .ok _ => fail "STRICT datatype failure was ignored after reopening"
  | .error message => unless message == "cannot store TEXT value in INT column t.n" do fail message
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok result => pure result | .error message => fail message
  let some (Statement.createStrictTable name columns constraints guard) := parsed.statements[0]?
    | fail "STRICT syntax marker was discarded"
  if (CoreTokenGrammar.check parsed.tokens #[.createTable name columns constraints guard]).isOk then
    fail "token replay accepted dropping STRICT semantics"

def expectCreateSchemaQualification : IO Unit := do
  let (literal, _) ← foreignStatement Core.State.empty "CREATE TABLE \"main.t\"(x);"
  let sql := "CREATE TABLE main.t(x ANY) STRICT;"
  let (state, _) ← foreignStatement literal sql
  unless (state.database.findTable? "t").isSome && (state.database.findTable? "main.t").isSome do
    fail "CREATE confused a main qualifier with a literal period"
  let some table := state.database.findTable? "t" | fail "qualified CREATE lost the table"
  unless table.catalogSQL == "CREATE TABLE t(x ANY) STRICT" do
    fail "qualified CREATE retained an incorrect catalog name"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok result => pure result | .error message => fail message
  let some (Statement.createStrictTable name columns constraints guard) := parsed.statements[0]?
    | fail "missing qualified STRICT declaration"
  unless name == "t" do fail "CREATE did not bind its lexical main qualifier"
  if (CoreTokenGrammar.check parsed.tokens #[.createStrictTable "main.t" columns constraints guard]).isOk then
    fail "token replay accepted a literal-period target for a qualified CREATE"
  let quoted := "CREATE TABLE \"main.u\"(x);"
  let parsedLiteral ← match CoreTokenGrammar.parseCertified quoted with
    | .ok result => pure result | .error message => fail message
  let some (Statement.createTable _ literalColumns literalConstraints literalGuard) := parsedLiteral.statements[0]?
    | fail "missing literal-period CREATE"
  if (CoreTokenGrammar.check parsedLiteral.tokens #[.createTable "u" literalColumns literalConstraints literalGuard]).isOk then
    fail "token replay split a quoted period into a CREATE qualifier"

def expectForeignKeys : IO Unit := do
  let (created, _) ← match CoreSourceSQL.execute Core.State.empty
      "CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES p(id));" with
    | .ok result => pure result | .error message => fail message
  let (enabled, _) ← foreignStatement created "PRAGMA foreign_keys=ON;"
  let (state, _) ← foreignStatement enabled "INSERT INTO c VALUES(1,1);"
  unless state.foreignKeys && state.foreignWrites.isEmpty do fail "foreign-key flag or private write scope leaked"
  for sql in ["INSERT OR IGNORE INTO c VALUES(2,99);", "DELETE FROM p;", "UPDATE c SET pid=99;"] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing foreign-key rejection"
    match CoreDerivedSQL.executeStatement state statement sql with
    | .ok _ => fail "foreign-key violation was accepted"
    | .error message => unless message == "FOREIGN KEY constraint failed" do fail message
  let (begun, _) ← foreignStatement state "BEGIN;"
  let (rolled, _) ← foreignStatement begun "ROLLBACK;"
  unless rolled.foreignKeys do fail "ROLLBACK changed the connection foreign-key flag"
  let some image := CoreFile.encode state.database | fail "foreign-key encoding failed"
  let some database := CoreDecode.decode image.fileBytes | fail "foreign-key decoding failed"
  let some table := database.findTable? "c" | fail "reopened child is missing"
  let some source := table.catalogSource | fail "reopened REFERENCES source is missing"
  let keys ← match source.compiledForeignKeys with
    | .ok keys => pure keys | .error message => fail message
  unless keys.length == 1 do fail "reopened REFERENCES program is missing"
  let sql := "CREATE TABLE d(x REFERENCES p(id));"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed | .error message => fail message
  let some (Statement.createTable name columns constraints guard) := parsed.statements[0]?
    | fail "missing REFERENCES declaration"
  let some column := columns[0]? | fail "missing REFERENCES column"
  let some key := column.references | fail "missing REFERENCES target"
  let forged := columns.set! 0 { column with references := some { key with table := "other" } }
  if (CoreTokenGrammar.check parsed.tokens #[.createTable name forged constraints guard]).isOk then
    fail "token replay accepted a changed REFERENCES target"

end SQLeanite.Tests
