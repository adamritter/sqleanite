import SQLeaniteTests.ExpectForeignKeyPragmas

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectCheckAddColumn : IO Unit := do
  let (state, _) ← match CoreSourceSQL.execute Core.State.empty
      "CREATE TABLE t(x INTEGER CHECK(x>0));INSERT INTO t VALUES(1),(3);" with
    | .ok result => pure result | .error message => fail message
  let sql := "ALTER TABLE t ADD y INTEGER DEFAULT 1 CHECK(y<=x);"
  let (next, _) ← match CoreSourceSQL.execute state sql with
    | .ok result => pure result | .error message => fail message
  let some table := next.database.findTable? "t" | fail "ALTER lost the table"
  unless table.rows.map (·.rowid) == (state.database.findTable? "t").toList.flatMap (fun t => t.rows.map (·.rowid)) do
    fail "ALTER changed existing rowids"
  unless next.lastInsertRowid == state.lastInsertRowid do fail "ALTER changed insertion register"
  match CoreSourceSQL.execute next "INSERT INTO t VALUES(2,9);" with
  | .ok _ => fail "ALTER lost its new CHECK"
  | .error message => unless message == "CHECK constraint failed: y<=x" do fail message
  match CoreSourceSQL.execute state "ALTER TABLE t ADD y DEFAULT 2 CHECK(y<=x);" with
  | .ok _ => fail "ALTER accepted an invalid existing row"
  | .error message => unless message == "CHECK constraint failed" do fail message
  let some image := CoreFile.encode next.database | fail "ALTER image encoding failed"
  let some reopened := CoreDecode.decode image.fileBytes | fail "ALTER image decoding failed"
  match CoreSQL.execute { database := reopened } "INSERT INTO t VALUES(-1,0);" with
  | .ok _ => fail "ALTER lost its old CHECK after reopening"
  | .error message => unless message == "CHECK constraint failed: x>0" do fail message

def expectInTable : IO Unit := do
  let (state, _) ← match CoreSourceSQL.execute Core.State.empty
      "CREATE TABLE t(x INTEGER);INSERT INTO t VALUES(1),(NULL);CREATE TABLE e(x);CREATE TABLE \"a.b\"(x);INSERT INTO \"a.b\" VALUES(3);" with
    | .ok result => pure result | .error message => fail message
  let sql := "SELECT 1 IN main.t,2 NOT IN t,NULL IN e,3 IN \"a.b\";"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing IN table query"
  let (next, output) ← match CoreDerivedSQL.executeStatement state statement sql with
    | .ok result => pure result | .error message => fail message
  let expected ← match [[Value.integer 1,.null,.integer 0,.integer 1]].mapM (List.mapM SQLSurface.value) with
    | .ok result => pure result | .error message => fail message
  unless output.flatMap (·.rows) == expected do fail "IN table shorthand changed names or NULL semantics"
  unless next.database.contents == state.database.contents do fail "IN table shorthand changed database"
  let correlated := "SELECT x,(SELECT -1 UNION ALL SELECT t.x LIMIT 1 OFFSET 1) FROM t ORDER BY rowid;"
  let parsedArms ← match CoreTokenGrammar.parseCertified correlated with
    | .ok parsed => pure parsed | .error message => fail message
  let some armStatement := parsedArms.statements[0]? | fail "missing correlated compound query"
  let (_, armOutput) ← match CoreDerivedSQL.executeStatement state armStatement correlated with
    | .ok result => pure result | .error message => fail message
  let armExpected ← match [[Value.integer 1,.integer 1],[.null,.null]].mapM (List.mapM SQLSurface.value) with
    | .ok result => pure result | .error message => fail message
  unless armOutput.flatMap (·.rows) == armExpected do fail "compound arm lost lexical outer bindings"
  let original := "SELECT 1 IN t WHERE 0;"
  let parsed ← match CoreTokenGrammar.parseCertified original with
    | .ok parsed => pure parsed | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "missing IN table replay query"
  for source in ["SELECT * FROM t WHERE 0", "SELECT * FROM e"] do
    let forged := { query with columns := #[{ expr := .inSubquery (.literal (.integer 1)) source }], where_ := none }
    if (CoreTokenGrammar.check parsed.tokens #[.select forged]).isOk then
      fail "token replay accepted a changed IN table or consumed an outer WHERE"

def expectSubquerySets : IO Unit := do
  let (state, _) ← match CoreSourceSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER);INSERT INTO t VALUES(1,1),(2,NULL);" with
    | .ok result => pure result | .error message => fail message
  let cases : List (String × List (List Value)) := [
    ("SELECT 1 IN (SELECT n FROM t),2 IN (SELECT n FROM t),NULL IN (SELECT n FROM t WHERE 0);",
      [[.integer 1,.null,.integer 0]]),
    ("SELECT id,n NOT IN (SELECT n FROM t) FROM t ORDER BY id;", [[.integer 1,.integer 0],[.integer 2,.null]]),
    ("SELECT EXISTS(SELECT abs(-9223372036854775808) FROM t);", [[.integer 1]]),
    ("SELECT EXISTS(SELECT abs(-9223372036854775808)+count(*) FROM t);", [[.integer 1]]),
    ("SELECT EXISTS(SELECT 1 FROM t WHERE id=1 OR abs(-9223372036854775808));", [[.integer 1]])]
  for (sql, expected) in cases do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing set subquery"
    let (next, output) ← match CoreDerivedSQL.executeStatement state statement sql with
      | .ok result => pure result | .error message => fail message
    let expected ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result | .error message => fail message
    unless output.flatMap (·.rows) == expected do fail s!"set-subquery result differs: {sql}"
    unless next.database.contents == state.database.contents do fail "set subquery changed database"
  let valuesSql := "SELECT 2 IN (VALUES(1),(2),(NULL)),EXISTS(VALUES(1,2));"
  let parsedValues ← match CoreTokenGrammar.parseCertified valuesSql with
    | .ok parsed => pure parsed | .error message => fail message
  let some valuesStatement := parsedValues.statements[0]? | fail "missing VALUES set query"
  let (_, valuesOutput) ← match CoreDerivedSQL.executeStatement state valuesStatement valuesSql with
    | .ok result => pure result | .error message => fail message
  let valuesExpected ← match [[Value.integer 1,.integer 1]].mapM (List.mapM SQLSurface.value) with
    | .ok result => pure result | .error message => fail message
  unless valuesOutput.flatMap (·.rows) == valuesExpected do fail "VALUES set query result differs"
  let sql := "SELECT 1 NOT IN (SELECT n FROM t);"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "missing NOT IN query"
  let some column := query.columns[0]? | fail "missing NOT IN column"
  let .unary .not argument := column.expr | fail "NOT IN lost its negation"
  let forged := { query with columns := query.columns.set! 0 { column with expr := argument } }
  if (CoreTokenGrammar.check parsed.tokens #[.select forged]).isOk then fail "token replay lost NOT IN negation"

def expectSubqueryFolding : IO Unit := do
  for sql in ["SELECT 0 AND (SELECT missing);", "SELECT 0 AND EXISTS(SELECT missing FROM absent);",
      "SELECT 0 AND 1 IN (SELECT missing);", "SELECT (SELECT missing) IN ();"] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing folded query"
    let (next, output) ← match CoreDerivedSQL.executeStatement Core.State.empty statement sql with
      | .ok result => pure result | .error message => fail message
    let expected ← match SQLSurface.value (.integer 0) with
      | .ok result => pure result | .error message => fail message
    unless output.flatMap (·.rows) == [[expected]] do fail "subquery was not folded before preparation"
    unless next.database.tables.isEmpty do fail "folded subquery changed database"
  for sql in ["SELECT 0 AND EXISTS(SELECT 1);", "SELECT 0 AND 1 IN (SELECT 1);"] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed | .error message => fail message
    let some (Statement.select query) := parsed.statements[0]? | fail "missing replay query"
    let some column := query.columns[0]? | fail "missing replay column"
    let expression := match column.expr with
      | .binary op left (.existsSubquery _) => .binary op left (.existsSubquery "SELECT 2")
      | .binary op left (.inSubquery arg _ negated) => .binary op left (.inSubquery arg "SELECT 2" negated)
      | other => other
    let forged := { query with columns := query.columns.set! 0 { column with expr := expression } }
    if (CoreTokenGrammar.check parsed.tokens #[.select forged]).isOk then
      fail "replay accepted changed captured subquery text"
  let parsed ← match CoreTokenGrammar.parseCertified "CREATE TABLE t(x CHECK(0 AND (SELECT 1)));" with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing folded CHECK"
  let (state, _) ← match CoreDerivedSQL.executeStatement Core.State.empty statement
      "CREATE TABLE t(x CHECK(0 AND (SELECT 1)));" with
    | .ok result => pure result | .error message => fail message
  match CoreSQL.execute state "INSERT INTO t VALUES(1);" with
  | .ok _ => fail "folded false CHECK accepted an insert"
  | .error message => unless message == "CHECK constraint failed: 0 AND (SELECT 1)" do fail message

def expectCheckUpdateDependencies : IO Unit := do
  let (state, _) ← match CoreSourceSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,x CHECK(x>0),y);" with
    | .ok result => pure result | .error message => fail message
  let some table := state.database.findTable? "t" | fail "missing CHECK table"
  let values ← match [Value.integer 1,.integer (-1),.integer 0].mapM SQLSurface.value with
    | .ok result => pure result | .error message => fail message
  let row ← match Core.Row.create table.schema values with
    | .ok row => pure row | .error message => fail message
  -- Model a file created while SQLite's ignore_check_constraints was enabled.
  let table ← match Core.Table.rebuild table.schema table.indexes [row] table.catalogSource with
    | .ok table => pure table | .error message => fail message
  let database ← match state.database.updateTable table with
    | .ok database => pure database | .error message => fail message
  let state := { state with database }
  let sql := "UPDATE t SET id=9,y=7 RETURNING *;"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing UPDATE"
  let (next, output) ← match CoreDerivedSQL.executeStatement state statement sql with
    | .ok result => pure result | .error message => fail message
  let expected ← match [Value.integer 9,.integer (-1),.integer 7].mapM SQLSurface.value with
    | .ok result => pure result | .error message => fail message
  unless output.flatMap (·.rows) == [expected] do fail "UPDATE checked an unrelated constraint or lost its row"
  unless next.lastInsertRowid == state.lastInsertRowid && next.lastChanges == 1 && next.totalChanges == 1 do
    fail "UPDATE changed insertion register or counters"
  match CoreSQL.execute next "UPDATE t SET x=x;" with
  | .ok _ => fail "same-value SET skipped its CHECK"
  | .error message => unless message == "CHECK constraint failed: x>0" do fail message
  let some table := next.database.findTable? "t" | fail "updated table disappeared"
  unless table.catalogSource.map (·.text) == (database.findTable? "t").bind (fun t => t.catalogSource.map (·.text)) do
    fail "UPDATE changed the retained CHECK source"
  let some image := CoreFile.encode next.database | fail "updated CHECK file encoding failed"
  let some reopened := CoreDecode.decode image.fileBytes | fail "updated CHECK file decoding failed"
  match CoreSQL.execute { database := reopened } "UPDATE t SET x=x;" with
  | .ok _ => fail "CHECK disappeared after reopening the updated file"
  | .error message => unless message == "CHECK constraint failed: x>0" do fail message

def expectCheckConstraints : IO Unit := do
  let declaration := "CREATE TABLE t(x CONSTRAINT low CHECK(x>0) CONSTRAINT high CHECK(x<10),CONSTRAINT other CHECK(x<>5));"
  let parsed ← match CoreTokenGrammar.parseCertified declaration with
    | .ok result => pure result | .error message => fail message
  let some (Statement.createTable name columns constraints guard) := parsed.statements[0]? | fail "missing CHECK table"
  let checks := CoreCheck.collect columns constraints
  unless checks.map CheckDef.diagnostic == ["low","high","other"] do fail "CHECK order or names changed"
  let some column := columns[0]? | fail "missing CHECK column"
  let forged := columns.set! 0 { column with earlierChecks := #[] }
  if (CoreTokenGrammar.check parsed.tokens #[.createTable name forged constraints guard]).isOk then
    fail "replay allowed an earlier CHECK to disappear"
  let some check := column.check | fail "missing final CHECK"
  let forged := columns.set! 0 { column with check := some { check with name := some "forged" } }
  if (CoreTokenGrammar.check parsed.tokens #[.createTable name forged constraints guard]).isOk then
    fail "replay allowed a forged CHECK diagnostic"
  let (state, _) ← match CoreSourceSQL.execute Core.State.empty declaration with
    | .ok result => pure result | .error message => fail message
  let (state, _) ← match CoreSourceSQL.execute state "INSERT INTO t VALUES(1),(NULL);" with
    | .ok result => pure result | .error message => fail message
  for (sql, expected) in [("INSERT INTO t VALUES(0);", "CHECK constraint failed: low"),
      ("UPDATE t SET x=11;", "CHECK constraint failed: high")] do
    match CoreSQL.execute state sql with
    | .ok _ => fail "Core DML skipped a retained CHECK"
    | .error message => unless message == expected do fail message
  let some image := CoreFile.encode state.database | fail "CHECK image encoding failed"
  let some database := CoreDecode.decode image.fileBytes | fail "CHECK image decoding failed"
  match CoreSQL.execute { database } "INSERT INTO t VALUES(5);" with
  | .ok _ => fail "CHECK disappeared across file encoding/decoding"
  | .error message => unless message == "CHECK constraint failed: other" do fail message

def expectZeroEncoding : IO Unit := do
  for encoding in [0,1,2,3] do
    unless CoreFileAdapter.utf8TextEncoding encoding == (encoding < 2) do
      fail "zero/UTF-8 encoding admission changed"
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/zero-encoding-regression.db"
    journal := ".lake/build/zero-encoding-regression.db-journal" }
  try
    for sql in ["", "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO t VALUES(1,'árvíz 😀');"] do
      let (state, _) ← match CoreSQL.execute Core.State.empty sql with
        | .ok result => pure result | .error message => fail message
      let some image := CoreFile.encode state.database | fail "zero encoding image construction failed"
      let bytes := [56,57,58,59].foldl (fun bytes index => bytes.set! index 0) image.fileBytes.toArray
      IO.FS.writeBinFile paths.main (ByteArray.mk bytes)
      let (reopened, _) ← CoreFileAdapter.reopenWithMetadata paths
      unless reopened.Equiv state.database do fail "zero encoding open changed the database"
      unless (← IO.FS.readBinFile paths.main).data == bytes do fail "read-only zero encoding open changed bytes"
  finally
    if ← paths.main.pathExists then IO.FS.removeFile paths.main
    if ← paths.journal.pathExists then IO.FS.removeFile paths.journal

def expectUniqueConstraints : IO Unit := do
  let mut state := Core.State.empty
  for sql in ["CREATE TABLE t(id INTEGER PRIMARY KEY,v INTEGER UNIQUE);", "INSERT INTO t VALUES(1,10);"] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing UNIQUE statement"
    match CoreDerivedSQL.executeStatement state statement sql with
    | .error message => fail message | .ok (next, _) => state := next
  let sql := "INSERT INTO t VALUES(2,10);"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing duplicate statement"
  match CoreDerivedSQL.executeStatement state statement sql with
  | .error message => unless message == "UNIQUE constraint failed: t.v" do fail message
  | .ok _ => fail "UNIQUE accepted a duplicate"
  let some image := CoreCatalogImage.encode 0 state.database (CoreFile.databaseHeader ⟨0, by decide⟩) {} []
    | fail "cannot encode automatic index"
  let source := CorePageSource.ofStorageImage (CoreCatalogImage.storage image)
  let ioSource : CoreDecode.IOPageSource := {
    pageCount := source.pageCount, readPage := fun page => pure (source.readPage page) }
  let some rows ← CoreSchemaRead.rows ioSource | fail "cannot read schema rows"
  let parsed ← match CoreTokenGrammar.parseCertified
      "SELECT count(*) FROM main.sqlite_schema WHERE type='index' AND sql IS NULL;" with
    | .ok parsed => pure parsed | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "missing schema query"
  match CoreSchemaRead.execute state query rows with
  | .error message => fail message
  | .ok (next, results) =>
      unless next.database.contents == state.database.contents do fail "schema read changed database"
      let actual ← (results.flatMap (·.rows)).mapM fun row => row.mapM fun cell =>
        match CoreExpr.value cell with
        | .ok (.integer value) => pure value
        | _ => fail "expected integer schema result"
      unless actual == [[1]] do fail "automatic index was not exposed with NULL SQL"
  let parsed ← match CoreTokenGrammar.parseCertified "CREATE TABLE a(v UNIQUE);" with
    | .ok parsed => pure parsed | .error message => fail message
  let some (Statement.createTable name columns constraints guard) := parsed.statements[0]?
    | fail "missing UNIQUE syntax"
  let some column := columns[0]? | fail "missing UNIQUE column"
  let forged := columns.set! 0 { column with unique := false }
  match CoreTokenGrammar.check parsed.tokens #[.createTable name forged constraints guard] with
  | .ok _ => fail "token replay accepted a removed UNIQUE constraint"
  | .error _ => pure ()

def expectIndexCatalogImage : IO Unit := do
  let mut state := Core.State.empty
  for sql in ["CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER);",
      "INSERT INTO t VALUES(1,10),(2,20);", "CREATE UNIQUE INDEX ix ON t(n);"] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing catalog statement"
    match CoreDerivedSQL.executeStatement state statement sql with
    | .error message => fail message
    | .ok (next, _) => state := next
  let old : GrowableStorage.Image PhysicalCodec.pageSize := {
    pageCount := 0, read := fun _ => Storage.Page.zero PhysicalCodec.pageSize }
  let sql := "CREATE UNIQUE INDEX ix ON t(n)"
  let entries : List CoreDecode.CatalogEntry := [
    { kind := "index", name := "ix", table := "t", rootPage := 0, sql := some sql }]
  let some image := CoreCatalogImage.encode 0 state.database (CoreFile.databaseHeader ⟨0, by decide⟩) {} [] entries
    | fail "catalog image encoding failed"
  let some checked := CoreCatalogImage.check old state.database image | fail "catalog component validation failed"
  unless checked.catalog.any (fun entry => entry.name == "ix" && entry.sql == some sql) do
    fail "original index declaration was not retained"
  if (CoreCatalogImage.check old Core.Database.empty image).isSome then
    fail "catalog checks accepted unrelated logical contents"
  let zero : CoreFile.Page := ⟨List.replicate PhysicalCodec.pageSize 0, by simp⟩
  let damaged := { image with pages := image.pages.reverse.drop 1 |>.reverse |>.concat zero }
  if (CoreCatalogImage.check old state.database damaged).isSome then
    fail "catalog checks accepted a damaged physical index"
  let wrong := entries.map fun entry => { entry with sql := some "CREATE INDEX ix ON t(n)" }
  let some table := state.database.findTable? "t" | fail "missing catalog table"
  let some index := table.indexes.head? | fail "missing catalog index"
  unless CoreCatalogImage.retainedSQL wrong table index == CoreFile.indexSQL table index do
    fail "catalog retention accepted mismatched uniqueness"

def expectUpsert : IO Unit := do
  let mut state := Core.State.empty
  for (sql, expected) in [
      ("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER);", []),
      ("INSERT INTO t VALUES(1,3),(2,7);", []),
      ("INSERT INTO t VALUES(1,9),(3,4),(1,2) ON CONFLICT(id) DO UPDATE SET n=t.n+excluded.n RETURNING id,n;", [[1,12],[3,4],[1,14]]),
      ("SELECT changes(),total_changes(),last_insert_rowid();", [[3,5,3]]),
      ("INSERT INTO t SELECT id,n+1 FROM t WHERE 1 ON CONFLICT(id) DO UPDATE SET n=excluded.n;", []),
      ("CREATE UNIQUE INDEX ix ON t(n);", []),
      ("INSERT INTO t VALUES(9,15) ON CONFLICT(n) DO UPDATE SET n=excluded.n+1 RETURNING id,n;", [[1,16]]),
      ("SELECT id,n FROM t ORDER BY id;", [[1,16],[2,8],[3,5]])] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing UPSERT statement"
    match CoreDerivedSQL.executeStatement state statement sql with
    | .error message => fail message
    | .ok (next, results) =>
        state := next
        let actual ← (results.flatMap (·.rows)).mapM fun row => row.mapM fun cell =>
          match CoreExpr.value cell with
          | .ok (.integer value) => pure value
          | _ => fail "expected integer UPSERT result"
        unless actual == expected do fail "incorrect UPSERT result"
  let sql := "INSERT INTO t VALUES(1,2) ON CONFLICT(id) DO NOTHING;"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed | .error message => fail message
  let some (Statement.upsert base alias clauses) := parsed.statements[0]? | fail "missing UPSERT syntax"
  let some first := clauses[0]? | fail "missing UPSERT clause"
  let forged := clauses.set! 0 { first with target := some #[.column none "n"] }
  match CoreTokenGrammar.check parsed.tokens #[.upsert base alias forged] with
  | .ok _ => fail "token replay accepted a changed UPSERT target"
  | .error _ => pure ()

def expectScalarSubqueries : IO Unit := do
  let mut state := Core.State.empty
  for (sql, expected) in [
      ("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER);", []),
      ("INSERT INTO t VALUES(1,3),(2,2),(3,7);", []),
      ("SELECT id,(SELECT max(n) FROM t) FROM t ORDER BY id;", [[1,7],[2,7],[3,7]]),
      ("SELECT a.id,(SELECT sum(b.n) FROM t b WHERE b.id<=a.id) FROM t a ORDER BY a.id;", [[1,3],[2,5],[3,12]]),
      ("SELECT CASE WHEN 1 THEN 7 ELSE (SELECT json('bad')) END;", [[7]]),
      ("SELECT a.id,(SELECT (SELECT a.n+1)) FROM t a ORDER BY id;", [[1,4],[2,3],[3,8]])] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing scalar-subquery statement"
    match CoreDerivedSQL.executeStatement state statement sql with
    | .error message => fail message
    | .ok (next, results) =>
        state := next
        let actual ← (results.flatMap (·.rows)).mapM fun row => row.mapM fun cell =>
          match CoreExpr.value cell with
          | .ok (.integer value) => pure value
          | _ => fail "expected integer scalar-subquery result"
        unless actual == expected do fail "incorrect scalar-subquery result"
  let parsed ← match CoreTokenGrammar.parseCertified "SELECT (SELECT 1);" with
    | .ok parsed => pure parsed | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "missing scalar query"
  let forged := { query with columns := #[{ expr := .scalarSubquery "SELECT 2" }] }
  match CoreTokenGrammar.check parsed.tokens #[.select forged] with
  | .ok _ => fail "token replay accepted a changed scalar subquery"
  | .error _ => pure ()

def expectWindowFunctions : IO Unit := do
  let realInput ← match SQLSurface.value (.real 2.5) with
    | .ok value => pure value | .error message => fail message
  let integerInput ← match SQLSurface.value (.integer 3) with
    | .ok value => pure value | .error message => fail message
  let accumulator := (SQLite.AggregateSum.State.step {} realInput).step integerInput
  let result ← match (accumulator.inverse realInput).sumResult with
    | .ok value => pure value | .error message => fail message
  match CoreExpr.value result with
  | .ok (.real value) => unless value == 3.0 do fail "incorrect sliding sum after inverse"
  | _ => fail "sliding sum lost its persistent REAL accumulator mode"
  let mut state := Core.State.empty
  for (sql, expected) in [
      ("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER);", []),
      ("INSERT INTO t VALUES(1,3),(2,2),(3,7);", []),
      ("SELECT id,row_number() OVER(ORDER BY n),sum(n) OVER(ORDER BY id ROWS BETWEEN 1 PRECEDING AND CURRENT ROW) FROM t ORDER BY id;",
        [[1,2,3],[2,1,5],[3,3,9]]),
      ("SELECT row_number() OVER(),sum(3) OVER();", [[1,3]]),
      ("WITH c AS (SELECT id,sum(n) OVER(ORDER BY id) s FROM t) SELECT * FROM c ORDER BY id;",
        [[1,3],[2,5],[3,12]])] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing window statement"
    match CoreDerivedSQL.executeStatement state statement sql with
    | .error message => fail message
    | .ok (next, results) =>
        if let .select _ := statement then
          unless next.database.tables.length == state.database.tables.length &&
              next.lastInsertRowid == state.lastInsertRowid do fail "window read changed connection state"
        state := next
        let actual ← (results.flatMap (·.rows)).mapM fun row => row.mapM fun cell =>
          match CoreExpr.value cell with
          | .ok (.integer value) => pure value
          | _ => fail "expected integer window result"
        unless actual == expected do fail "incorrect partition/order/frame result"
  let parsed ← match CoreTokenGrammar.parseCertified "SELECT row_number() OVER(ORDER BY id) FROM t;" with
    | .ok parsed => pure parsed | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "missing window query"
  let expression := Expr.call "__sqlean_window" #[.call "row_number" #[] false, .literal (.text "(ORDER BY id DESC)")] false
  let forged := { query with columns := #[{ expr := expression }] }
  match CoreTokenGrammar.check parsed.tokens #[.select forged] with
  | .ok _ => fail "token replay accepted a changed window ordering"
  | .error _ => pure ()

def expectJsonTableFunctions : IO Unit := do
  for (sql, expected) in [
      ("WITH j AS (SELECT value FROM json_each('[[1]]')) SELECT json_array(value) FROM j;", Value.text "[[1]]"),
      ("WITH j AS MATERIALIZED (SELECT value FROM json_each('[[1]]')) SELECT json_array(value) FROM j;", Value.text "[\"[1]\"]"),
      ("SELECT sum(atom) FROM json_tree('[1,[2,3]]');", Value.integer 6),
      ("SELECT max(id) FROM json_tree('[1,[2,3]]');", Value.integer 6),
      ("SELECT json_array(value) FROM json_each('[[1]]');", Value.text "[[1]]"),
      ("SELECT json_array(value) FROM (SELECT value FROM json_each('[[1]]'));", Value.text "[[1]]")] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed
      | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing JSON table statement"
    match CoreDerivedSQL.executeStatement Core.State.empty statement sql with
    | .error message => fail message
    | .ok (next, results) =>
        unless next.database.tables.isEmpty && next.lastInsertRowid == 0 do
          fail "JSON table materialization escaped its statement"
        let some row := (results.flatMap (·.rows))[0]? | fail "missing JSON table result"
        let some cell := row[0]? | fail "missing JSON table cell"
        match CoreExpr.value cell with
        | .error message => fail message
        | .ok value => unless value == expected do fail "incorrect JSON table value or subtype"

  let sql := "WITH j AS MATERIALIZED (SELECT value FROM json_each('[[1]]')) SELECT value FROM j;"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed
    | .error message => fail message
  let some (Statement.withCte name aliases source body _) := parsed.statements[0]?
    | fail "missing CTE materialization hint"
  match CoreTokenGrammar.check parsed.tokens #[.withCte name aliases source body .default] with
  | .ok _ => fail "token replay accepted a changed CTE materialization hint"
  | .error _ => pure ()

end SQLeanite.Tests
