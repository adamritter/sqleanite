import SQLeaniteTests.ExpectForeignKeyPragmas

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectUTF16Reads : IO Unit := do
  for encoding in [2,3] do
    for value in ["ASCII", "Árvíztűrő", "你好", "😀𝄞", "A\x00B", ""] do
      let bytes := value.toUTF8.data
      let stored := SQLite.TextEncoding.toStorage encoding bytes
      unless SQLite.TextEncoding.fromStorage encoding stored == bytes do
        fail "UTF-16 byte translation lost valid Unicode or NUL"
      if bound : stored.toList.length < PhysicalCodec.textByteLimit then
        let field := PhysicalCodec.Text.recordField ⟨stored.toList,bound⟩
        let some decoded := CoreTextEncoding.field encoding field | fail "UTF-16 record field was rejected"
        let some (.text text) := PhysicalCodec.decodeValueField decoded | fail "UTF-16 TEXT changed storage class"
        unless text.bytes == bytes.toList do fail "physical UTF-16 record lost text bytes"
      else fail "small UTF-16 fixture exceeded the physical text bound"
  let (created,_) ← foreignStatement Core.State.empty "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);"
  let (base,_) ← foreignStatement created "INSERT INTO t VALUES(1,'a',2),(2,'Ā',4),(3,'😀',6);"
  for encoding in [2,3] do
    let state := { base with catalog := { base.catalog with current := { base.catalog.current with textEncoding := encoding } } }
    let binary := if encoding == 2 then 0 else 1
    let literalHex := if encoding == 2 then "6100" else "0061"
    let upperHex := if encoding == 2 then "4100" else "0041"
    let numberHex := if encoding == 2 then "34003200" else "00340032"
    let cases : List (String × List (List Value)) := [
      ("SELECT 'a'<'Ā',char(97)<char(256);", [[.integer binary,.integer binary]]),
      ("SELECT hex('a'),hex(upper('a')),octet_length('a'),octet_length(upper('a'));", [[.text literalHex,.text upperHex,.integer 2,.integer 2]]),
      ("SELECT typeof(CAST(42 AS TEXT)),hex(CAST(42 AS TEXT));", [[.text "text",.text numberHex]]),
      ("SELECT hex(CAST(CAST(X'41' AS TEXT) AS BLOB));", [[.text ""]]),
      ("SELECT count(*) FROM t WHERE id='1';", [[.integer 1]])]
    for (sql,expected) in cases do
      let (_,results) ← foreignStatement state sql
      let expected ← expected.mapM (·.mapM fun value => match SQLSurface.value value with
        | .ok value => pure value | .error message => fail message)
      unless results.flatMap (·.rows) == expected do fail s!"UTF-16 runtime encoding or BINARY comparison changed: {sql}"
  let parsed := CoreTokenGrammar.parseCertified "SELECT __sqlean_encoded('input',2,'a');"
  match parsed with
  | .error message => unless message == "no such function: __sqlean_encoded" do fail message
  | .ok _ => fail "compiler-owned encoding annotations were accepted as public SQL"


def expectUTF16Edges : IO Unit := do
  let (created,_) ← foreignStatement Core.State.empty "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);"
  let (base,_) ← foreignStatement created "INSERT INTO t VALUES(1,'a'),(2,'Ā'),(3,'😀'),(4,'');"
  let some stored := base.database.findTable? "t" | fail "missing native TEXT fixture"
  let one ← match SQLSurface.value (.integer 1) with
    | .ok value => pure value | .error message => fail message
  for encoding in [2,3] do
    let state := { base with catalog := { base.catalog with current := { base.catalog.current with textEncoding := encoding } } }
    let values := if encoding == 2 then ["Ā","","😀","a","z"] else ["a","z","Ā","😀",""]
    let ranks := if encoding == 2 then [4,1,3,2] else [1,2,3,4]
    for (sql,expected) in [
        ("SELECT v FROM t UNION SELECT 'z' ORDER BY v;", values.map fun value => [Value.text value]),
        ("SELECT substr(v,1) AS x FROM t UNION ALL SELECT 'z' ORDER BY x;", values.map fun value => [Value.text value]),
        ("SELECT id,row_number() OVER(ORDER BY v) FROM t ORDER BY id;",
          ranks.zipIdx.map fun (rank,index) => [Value.integer (index+1),Value.integer rank])] do
      let (next,results) ← foreignStatement state sql
      let expected ← expected.mapM (·.mapM fun value => match SQLSurface.value value with
        | .ok value => pure value | .error message => fail message)
      unless results.flatMap (·.rows) == expected do fail s!"encoded compound/window order changed: {sql}"
      unless next.catalog.current.contents == state.catalog.current.contents &&
          CoreFileEngine.databaseContents next.database == CoreFileEngine.databaseContents state.database do
        fail "encoded read changed the physical connection state"
    let raw : Array UInt8 := if encoding == 2 then #[0,216,65,0] else #[216,0,0,65]
    let expectedHex := if encoding == 2 then "00D84100" else "D8000041"
    if bound : raw.toList.length < PhysicalCodec.textByteLimit then
      let field := PhysicalCodec.Text.recordField ⟨raw.toList,bound⟩
      let physical := [FileFormat.RecordField.null,field]
      let some fields := CoreTextEncoding.fields encoding physical | fail "native record translation failed"
      let .integer rowid := one | fail "missing INTEGER rowid"
      let some row := CoreRecord.decodeRowFields stored.schema rowid fields | fail "native row decode failed"
      let origins := CoreTextEncoding.origins encoding stored.schema row physical
      unless origins.length == 1 do fail "nonreversible native bytes were not retained exactly once"
      let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := "t", storedTexts := origins }
      let scalar ← match ctx.lookupScalar row.values none "v" with
        | .ok scalar => pure scalar | .error message => fail message
      unless scalar.textEncoding == encoding && scalar.encodedText == some raw do
        fail "source column lost its original native bytes"
      let encoded := SQLite.TextEncoding.bind encoding 10 (.call "hex" #[.column none "v"] false)
      match ctx.eval row.values encoded with
      | .ok (.text value) => unless value == expectedHex do fail "native column hex changed storage bytes"
      | _ => fail "native column hex was not TEXT"
      let stale := origins.map fun origin => { origin with bytes := #[65,0] }
      let staleCtx := { ctx with storedTexts := stale }
      match staleCtx.lookupScalar row.values none "v" with
      | .ok result => unless result.encodedText.isNone do fail "mismatched native bytes were attached to a logical value"
      | .error message => fail message
      let observed ← IO.mkRef ([] : List FileFormat.RecordField)
      let source : CoreDecode.IOPageSource := {
        pageCount := 0
        readPage := fun _ => pure none
        observeRow := some (fun _ _ actual => observed.set actual) }
      let result ← CoreDecode.finishRowRead stored.schema source rowid physical fields
      unless result == some row do fail "native observation changed the decoded row"
      unless (← observed.get) == physical do fail "observer received translated fields instead of physical fields"
      observed.set []
      let invalid ← CoreDecode.finishRowRead stored.schema source rowid physical
        [PhysicalCodec.Value.recordField one,field]
      unless invalid.isNone && (← observed.get).isEmpty do fail "invalid record reached native byte observation"
    else fail "small native byte fixture exceeded the text bound"


def expectUTF16Provenance : IO Unit := do
  let (created,_) ← foreignStatement Core.State.empty "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);"
  let (base,_) ← foreignStatement created "CREATE VIEW q AS SELECT id,v FROM t;"
  let some stored := base.database.findTable? "t" | fail "missing native provenance schema"
  let one ← match SQLSurface.value (.integer 1) with
    | .ok value => pure value | .error message => fail message
  let .integer rowid := one | fail "native provenance rowid was not INTEGER"
  for encoding in [2,3] do
    let raw : Array UInt8 := if encoding == 2 then #[0,216,65,0] else #[216,0,0,65]
    let nativeHex := if encoding == 2 then "00D84100" else "D8000041"
    let concatHex := if encoding == 2 then "00D841007800" else "D80000410078"
    let canonicalHex := if encoding == 2 then "00D841DC" else "D800DC41"
    if bound : raw.toList.length < PhysicalCodec.textByteLimit then
      let physical := [FileFormat.RecordField.null,PhysicalCodec.Text.recordField ⟨raw.toList,bound⟩]
      let some fields := CoreTextEncoding.fields encoding physical | fail "native provenance field decode failed"
      let some row := CoreRecord.decodeRowFields stored.schema rowid fields | fail "native provenance row decode failed"
      let table ← match Core.Table.rebuild stored.schema [] [row] stored.catalogSource with
        | .ok value => pure value | .error message => fail message
      let database ← match Core.Database.rebuild [table] with
        | .ok value => pure value | .error message => fail message
      let state := { base with database, catalog := { base.catalog with
        current := { base.catalog.current with textEncoding := encoding }
        storedTexts := CoreTextEncoding.origins encoding stored.schema row physical } }
      let cases : List (String × List (List Value)) := [
        ("SELECT hex(v) FROM q;", [[.text nativeHex]]),
        ("SELECT hex(v) FROM (SELECT v FROM t);", [[.text nativeHex]]),
        ("WITH c AS MATERIALIZED(SELECT v FROM t) SELECT hex(v) FROM c;", [[.text nativeHex]]),
        ("SELECT hex(a.v),hex(b.v) FROM t a JOIN t b ON a.id=b.id;", [[.text nativeHex,.text nativeHex]]),
        ("SELECT hex(v),row_number() OVER(ORDER BY id) FROM t;", [[.text nativeHex,.integer 1]]),
        ("SELECT hex(min(v)),hex(max(v)) FROM t;", [[.text nativeHex,.text nativeHex]]),
        ("SELECT hex(v||'x'),hex(v||v) FROM t;", [[.text concatHex,.text (nativeHex++nativeHex)]]),
        (s!"SELECT v=CAST(X'{canonicalHex}' AS TEXT) FROM t;", [[.integer 0]])]
      for (sql,expected) in cases do
        let (next,results) ← foreignStatement state sql
        let expected ← expected.mapM (·.mapM fun value => match SQLSurface.value value with
          | .ok value => pure value | .error message => fail message)
        unless results.flatMap (·.rows) == expected do fail s!"native TEXT provenance lost across a SQL boundary: {sql}"
        unless CoreFileEngine.databaseContents next.database == CoreFileEngine.databaseContents state.database &&
            next.catalog.current.contents == state.catalog.current.contents do
          fail "private native representation escaped into persistent contents"
    else fail "small native provenance fixture exceeded text bound"


end SQLeanite.Tests
