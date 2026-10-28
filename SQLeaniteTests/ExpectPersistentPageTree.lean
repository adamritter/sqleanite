import SQLeaniteTests.ExpectWideCIndexCertificate

namespace SQLeanite.Tests
open SQLeanite

def expectPersistentPageTree : IO Unit := do
  let entries : List (PagedBTree.Entry Nat) :=
    [(1, 10), (2, 20), (3, 30), (5, 50), (6, 60), (7, 70)]
  let store := PersistentPageTree.Store.build 10 entries
  unless store.root.erase.toList == entries do
    fail "persistent page-tree bulk builder changed its logical entries"
  let rootPage := store.root.rootId
  let updated := store.insert 4 40
  unless updated.root.rootId == rootPage do
    fail "persistent page-tree insertion moved the stable root page"
  let expected := PagedBTree.orderedInsert 4 40 entries
  unless updated.root.erase.toList == expected do
    fail "persistent page-tree insertion disagreed with its abstraction"
  let dirty := PersistentPageTree.changedPages store.root updated.root
  unless dirty.length < updated.root.pages.length do
    fail "persistent page-tree insertion rewrote every materialized page"
  let logical ← match CoreSQL.execute Core.State.empty "
      CREATE TABLE a(id INTEGER PRIMARY KEY,v);
      CREATE TABLE b(id INTEGER PRIMARY KEY,v);
      INSERT INTO a VALUES(1,'x'),(2,'y'),(3,'z');
      INSERT INTO b VALUES(8,'q');" with
    | .ok (state, _) => pure state.database
    | .error message => fail s!"Core page-state setup failed: {message}"
  let physical ← match CoreChunkPageState.State.build? logical with
    | some state => pure state
    | none => fail "packed Core page-state builder rejected valid logical tables"
  unless physical.tables.map (fun table => table.table.contents) ==
      logical.tables.map Core.Table.contents do
    fail "Core physical page state does not represent all logical tables"
  let rootPages := physical.tables.map CoreChunkPageState.TableState.rootPage
  unless rootPages.eraseDups == rootPages do
    fail "Core physical page state assigned duplicate table roots"
  unless physical.activePageIds.eraseDups == physical.activePageIds do
    fail "Core physical page state assigned duplicate active pages"
  let image ← match CorePageCodec.encodeBulk logical with
    | some image => pure image
    | none => fail "stable-page bulk encoder rejected a valid Core database"
  let reopened ← match CoreDecode.decode image.fileBytes with
    | some database => pure database
    | none => fail "general decoder rejected the stable-page bulk image"
  unless reopened.Equiv logical do
    fail "stable-page bulk encoding changed the logical database"
  let path : System.FilePath :=
    ".lake/build/sqleanite-stable-page-bulk.db"
  IO.FS.writeBinFile path (ByteArray.mk image.fileBytes.toArray)
  let check ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT count(*) FROM a; SELECT count(*) FROM b;"] }
  unless check.exitCode == 0 && check.stdout == "ok\n3\n1\n" do
    fail s!"sqlite3 rejected stable-page bulk encoding: {check.stderr}{check.stdout}"
  let wideImage ← match CoreWidePageCodec.encodeBulkInline logical with
    | some image => pure image
    | none => fail "wide physical codec rejected inline Core tables"
  let wideReopened ← match CoreDecode.decode wideImage.fileBytes with
    | some database => pure database
    | none => fail "general decoder rejected the wide physical image"
  unless wideReopened.Equiv logical do
    fail "wide physical encoding changed the logical database"
  let wideSource : CoreDecode.PageSource :=
    .ofList (wideImage.pages.map (fun page => page.bytes))
  let wideState ← match CoreWidePageLoad.load? wideSource logical with
    | some state => pure state
    | none => fail "validating loader rejected the wide physical image"
  unless wideState.tables.map (fun table => table.table.contents) ==
      logical.tables.map Core.Table.contents do
    fail "wide validating loader detached topology from logical tables"
  let widePath : System.FilePath :=
    ".lake/build/sqleanite-wide-page-bulk.db"
  IO.FS.writeBinFile widePath (ByteArray.mk wideImage.fileBytes.toArray)
  let wideCheck ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[widePath.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT count(*) FROM a; SELECT count(*) FROM b;"] }
  unless wideCheck.exitCode == 0 && wideCheck.stdout == "ok\n3\n1\n" do
    fail s!"sqlite3 rejected wide physical encoding: {wideCheck.stderr}{wideCheck.stdout}"
  -- The 130k-row YCSB census contained exactly 43,333 byte-budgeted chunks.
  -- A physical 2-3 topology used 43,326 interior pages for them.  The wide
  -- topology gives each full-page chunk one leaf and up to 256 children per
  -- interior; the schema-aware chunker fills that leaf's byte budget.
  let censusEntries : List (PagedBTree.Entry Nat) :=
    (List.range 43333).map fun key => (key, key)
  let wide ← match WidePageTree.build censusEntries with
    | some plan => pure plan
    | none => fail "high-fanout physical builder exhausted its total fuel"
  unless wide.toList == censusEntries && wide.leafCount == 43333 &&
      wide.interiorCount == 171 && wide.pageCount == 43504 do
    fail "high-fanout physical builder regressed to sparse 2-3 page topology"
  have censusOrdered : censusEntries.Pairwise
      (fun left right => left.1 < right.1) := by
    simpa [censusEntries, List.pairwise_map] using
      (List.pairwise_lt_range (n := 43333))
  let wideStore ← match WidePageTree.Store.build? 2 censusEntries
      censusOrdered with
    | some store => pure store
    | none => fail "numbered high-fanout store exhausted its total fuel"
  unless wideStore.toList == censusEntries &&
      wideStore.root.leafCount == 43333 &&
      wideStore.root.interiorCount == 171 &&
      wideStore.root.pageCount == 43504 do
    fail "numbered high-fanout store changed contents or page topology"
  -- SQLite reserves page 262145 for the POSIX pending-byte lock.  Exercise
  -- the otherwise million-row-only boundary with a tiny, shifted fixture.
  let pending := WidePageTree.pendingBytePage
  unless WidePageTree.allocatedPage (pending - 1) 0 == pending - 1 &&
      WidePageTree.allocatedPage (pending - 1) 1 == pending + 1 &&
      WidePageTree.allocatedPage (pending - 1) 2 == pending + 2 do
    fail "wide allocator did not skip SQLite's pending-byte page"
  let boundaryEntries : List (PagedBTree.Entry Nat) := [(0, 0), (1, 1)]
  have boundaryOrdered : boundaryEntries.Pairwise
      (fun left right => left.1 < right.1) := by decide
  let boundaryStore ← match WidePageTree.Store.build? (pending - 1)
      boundaryEntries boundaryOrdered with
    | some store => pure store
    | none => fail "wide pending-byte boundary fixture failed to build"
  if boundaryStore.root.pageIds.contains pending then
    fail "wide topology assigned SQLite's pending-byte page"
  -- Fill a complete 256-child root, then append once.  This forces both a
  -- leaf split and root split, and checks that the public root page remains
  -- stable while three fresh physical pages are allocated.
  let splitEntries : List (PagedBTree.Entry Nat) :=
    (List.range 256).map fun key => (key, key)
  have splitOrdered : splitEntries.Pairwise
      (fun left right => left.1 < right.1) := by
    simpa [splitEntries, List.pairwise_map] using
      (List.pairwise_lt_range (n := 256))
  match splitBuilt : WidePageTree.Store.build? 2 splitEntries splitOrdered with
  | none => fail "wide split fixture exhausted its total fuel"
  | some splitStore =>
      have afterSplitEntries : ∀ old ∈ splitStore.toList, old.1 < 256 := by
        intro old member
        rw [WidePageTree.Store.build?_toList splitBuilt] at member
        rcases List.mem_map.mp member with ⟨key, keyMember, rfl⟩
        simpa using keyMember
      let appended ← match splitStore.append? (256, 256)
          afterSplitEntries with
        | some result => pure result
        | none => fail "wide append failed to propagate a full-root split"
      unless appended.value.toList == splitEntries ++ [(256, 256)] &&
          appended.value.root.rootId == splitStore.root.rootId &&
          appended.value.root.leafCount == 257 &&
          appended.value.root.interiorCount == 3 &&
          appended.value.root.pageCount == 260 do
        fail "wide append changed contents, root identity, or split topology"

def expectCheckedTablePages : IO Unit := do
  let keys : List Core.Integer := [
    ⟨-9223372036854775808, by decide, by decide⟩,
    ⟨-1, by decide, by decide⟩, ⟨1, by decide, by decide⟩,
    ⟨127, by decide, by decide⟩, ⟨128, by decide, by decide⟩,
    ⟨16383, by decide, by decide⟩, ⟨16384, by decide, by decide⟩,
    ⟨9223372036854775807, by decide, by decide⟩]
  let missing : List Core.Integer := [⟨-2, by decide, by decide⟩,
    ⟨0, by decide, by decide⟩, ⟨2, by decide, by decide⟩,
    ⟨129, by decide, by decide⟩, ⟨16385, by decide, by decide⟩]
  let makePage := fun (pageKeys : List Core.Integer) => Id.run do
    let cells := pageKeys.map fun key =>
      [0] ++ FileFormat.encodeVarint (FileFormat.signedInteger64Bits key)
    let headerEnd := 8 + 2 * cells.length
    let mut offset := headerEnd
    let mut pointers := []
    for cell in cells do
      pointers := pointers ++ FileFormat.encodeUnsignedFixed 2 offset
      offset := offset + cell.length
    let data := [13, 0, 0] ++ FileFormat.encodeUnsignedFixed 2 cells.length ++
      FileFormat.encodeUnsignedFixed 2 headerEnd ++ [0] ++ pointers ++ cells.flatten
    return ByteArray.mk ((data ++ List.replicate (4096 - data.length) 0).toArray)
  for count in List.range (keys.length + 1) do
    let pageKeys := keys.take count
    let bytes := makePage pageKeys
    let some _ := Runtime.TablePage.decode? bytes | fail "checked page rejected ordered keys"
    for capacity in [0, 1] do
      let pager : Runtime.ReadPager.Pager := {
        pageCount := 1, pageSize := 4096, capacity
        pages := ← IO.mkRef {}, readAt := fun _ _ => pure bytes }
      let cursor ← Runtime.TableCursor.create pager 1
      for key in (keys ++ missing) ++ (keys ++ missing).reverse do
        let some actual ← cursor.seek key 2 | fail "checked cursor rejected a valid leaf"
        unless actual.map (·.key) == pageKeys.find? (· == key) do
          fail "binary seek disagrees with logical keys at a varint/signed boundary"
        if let some cell := actual then
          unless cell.input == cell.bytes.toList.drop cell.offset do
            fail "cell view changed its shared reference bytes"
      unless (← cursor.views.get).size ≤ capacity do
        fail "checked-page cache exceeded capacity"
      unless (← cursor.seek ⟨0, by decide, by decide⟩ 0).isNone do
        fail "retained cursor bypassed zero traversal fuel"
  let valid := makePage (keys.take 3)
  let badPointer := (valid.set! 8 0).set! 9 7
  let badCount := (valid.set! 3 255).set! 4 255
  let unordered := makePage keys.reverse
  for bytes in [badPointer, badCount, unordered, valid.extract 0 10, valid.set! 0 2] do
    unless (Runtime.TablePage.decode? bytes).isNone do
      fail "checked page accepted corrupt pointers/header or unordered keys"
    let pager : Runtime.ReadPager.Pager := {
      pageCount := 1, pageSize := bytes.size, capacity := 1
      pages := ← IO.mkRef {}, readAt := fun _ _ => pure bytes }
    let cursor ← Runtime.TableCursor.create pager 1
    unless (← cursor.seek ⟨0, by decide, by decide⟩ 2).isNone && (← cursor.views.get).isEmpty do
      fail "corrupt page became a successful miss or entered the page-view cache"

def expectReadPagerBoundary : IO Unit := do
  let reads ← IO.mkRef 0
  let pager : Runtime.ReadPager.Pager := {
    pageCount := 2
    pageSize := 4
    capacity := 1
    pages := ← IO.mkRef {}
    readAt := fun offset _ => do
      reads.modify (· + 1)
      if offset == 0 then return ByteArray.mk #[1, 2, 3, 4]
      else return ByteArray.mk #[5, 6, 7, 8] }
  unless (← pager.get 0).isNone && (← pager.get 3).isNone &&
      (← reads.get) == 0 do
    fail "pager read an out-of-range page"
  for page in [1, 1, 2, 2] do
    let some bytes ← pager.get page | fail "pager rejected a complete page"
    let expected := if page == 1 then [1, 2, 3, 4] else [5, 6, 7, 8]
    unless bytes.toList == expected do fail "pager changed page bytes"
  unless (← reads.get) == 3 && (← pager.pages.get).size == 1 do
    fail "pager did not reuse cached bytes or exceeded its bound"
  let short : Runtime.ReadPager.Pager := {
    pager with
    pages := ← IO.mkRef {}
    readAt := fun _ _ => pure (ByteArray.mk #[1, 2, 3]) }
  unless (← short.get 1).isNone && (← short.pages.get).isEmpty do
    fail "pager retained a truncated page"

def expectCachedPrimaryEdgeRows : IO Unit := do
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-cached-primary-edges.db"
    journal := ".lake/build/sqleanite-cached-primary-edges.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  let connection ← CoreFileEngine.create .system paths
  let large := String.mk (List.replicate 9000 'z')
  let setup := s!"CREATE TABLE edge(value TEXT,id INTEGER PRIMARY KEY);
    INSERT INTO edge VALUES('{large}',-7),('zero',0),('positive',17);"
  match ← CoreFileEngine.execute connection setup with
  | .error message => fail s!"cached primary edge setup: {message}"
  | .ok _ => pure ()
  let state ← CoreFileEngine.snapshot connection
  let query := "SELECT id,value FROM edge WHERE id=-7;
    SELECT value,id FROM edge WHERE id=0;
    SELECT id,value FROM edge WHERE id=17;
    SELECT id,value FROM edge WHERE id=-8;
    SELECT id,value FROM edge WHERE id=-7;"
  let expected ← match CoreSQL.execute state query with
    | .ok (_, results) => pure results
    | .error message => fail s!"cached primary edge reference: {message}"
  match ← CoreLazyFileEngine.execute? paths query with
  | some (.ok actual) =>
      unless actual.map (·.rows) == expected.map (·.rows) do
        fail "cached primary changed signed, overflow, or non-first key rows"
  | _ => fail "cached primary edge rows missed the generated fast path"
  -- Each new batch owns a fresh cache, so a durable write must be visible.
  match ← CoreFileEngine.execute connection
      "UPDATE edge SET value='updated' WHERE id=-7;" with
  | .error message => fail s!"cached primary edge update: {message}"
  | .ok _ => pure ()
  match ← CoreLazyFileEngine.execute? paths
      "SELECT value FROM edge WHERE id=-7;" with
  | some (.ok [{ rows := [[.text value]], .. }]) =>
      unless value.bytes == "updated".toUTF8.toList do
        fail "primary batch reused stale pages after a write"
  | _ => fail "updated primary row did not remain readable"

def expectCertifiedCoreTokenGrammar : IO Unit := do
  let sql := "CREATE TABLE usertable(ycsb_key TEXT PRIMARY KEY,field0 TEXT);\n    BEGIN; INSERT INTO usertable VALUES('user0001','payload');\n    SELECT field0 FROM usertable WHERE (ycsb_key='user0001'); COMMIT;"
  let certificate ← match CoreTokenGrammar.parseCertified sql with
    | .ok certificate => pure certificate
    | .error message => fail s!"certified Core grammar rejected its exact schema: {message}"
  unless certificate.statements.size == 5 do
    fail "certified Core grammar lost a statement boundary"
  match CoreTokenGrammar.check certificate.tokens #[.rollback] with
  | .error _ => pure ()
  | .ok () => fail "independent Core grammar admitted a mismatched AST"

def expectSQLiteScalarCore : IO Unit := do
  let samples : List (String × Value) := [
    ("-1.5", .real (-1.5)), ("-7/3", .integer (-2)), ("7%-3", .integer 1),
    ("9223372036854775807+1", .real (Float.ofInt 9223372036854775808)),
    ("-9223372036854775808/-1", .real (Float.ofInt 9223372036854775808)),
    ("1/0", .null), ("0*1e999", .null), ("5.5%2", .real 1.0),
    ("'12x'+3", .integer 15), ("NOT '0.5x'", .integer 0),
    ("-1>>64", .integer (-1)), ("1<<-1", .integer 0),
    ("CAST('123e+5' AS INTEGER)", .integer 123),
    ("CAST('1.0' AS NUMERIC)", .integer 1),
    ("CAST('9223372036854775808' AS INTEGER)", .integer 9223372036854775807),
    ("length('árvíz')", .integer 5), ("octet_length('árvíz')", .integer 7),
    ("upper('Árvíz abc')", .text "ÁRVíZ ABC"),
    ("CASE 1 WHEN 1.0 THEN 7 ELSE abs(-9223372036854775808) END", .integer 7),
    ("coalesce(NULL,7,abs(-9223372036854775808))", .integer 7),
    ("iif(0,1,NULL,2,1,3,abs(-9223372036854775808))", .integer 3)]
  for (expression, expected) in samples do
    let (_, results) ← match CoreSQL.execute Core.State.empty
        s!"CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,{expression}); SELECT v FROM t;" with
      | .ok outcome => pure outcome
      | .error message => fail s!"Core scalar {expression}: {message}"
    let value ← match SQLSurface.value expected with
      | .ok value => pure value
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [[value]] do
      fail s!"Core scalar {expression}: wrong typed result"

def expectSQLiteTextFunctions : IO Unit := do
  let samples : List (String × Value) := [
    ("hex(X'00FF80')", .text "00FF80"), ("hex(NULL)", .text ""),
    ("unhex('41 42',' ')", .blob #[65, 66]), ("unhex('4 142',' ')", .null),
    ("substr('árvíz',-3,2)", .text "ví"), ("substr('abcdef',3,-2)", .text "ab"),
    ("substr('abc',0,2)", .text "a"), ("substr(X'',1)", .null),
    ("substr(X'00FF41',2,2)", .blob #[255, 65]),
    ("instr('a🙂β','β')", .integer 3), ("instr('abc','')", .integer 1),
    ("trim('🙂abc🙂','🙂')", .text "abc"), ("ltrim(' x ')", .text "x "),
    ("rtrim(' x ')", .text " x"), ("replace('ababa','aba','X')", .text "Xba"),
    ("replace('a','',NULL)", .text "a"), ("concat(NULL,'',1)", .text "1"),
    ("concat_ws('-',NULL,'','')", .text "-"), ("concat_ws(NULL,'a')", .null),
    ("char(65,128578)", .text "A🙂"), ("char()", .text ""),
    ("unicode('🙂')", .integer 128578), ("unicode('')", .null),
    ("unicode(X'FF')", .integer 65533),
    ("unicode(X'CBBEB9A28F89934749')", .integer (-1182207405)), ("unicode(char(65535))", .integer 65533),
    ("quote('O''Brien')", .text "'O''Brien'"), ("quote(1e999)", .text "9.0e+999"),
    ("zeroblob(3)", .blob #[0, 0, 0]), ("sign('1x')", .null),
    ("sign('-1.5')", .integer (-1)), ("sign(X'31')", .null),
    ("typeof(min(1,1.0))", .text "real"), ("typeof(max(1,1.0))", .text "integer")]
  for (expression, expected) in samples do
    let sql := s!"CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,{expression}); SELECT v FROM t;"
    match CoreTokenGrammar.parseStatements sql with
    | .error message => fail s!"text function certificate {expression}: {message}"
    | .ok _ => pure ()
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok outcome => pure outcome
      | .error message => fail s!"text function {expression}: {message}"
    let value ← match SQLSurface.value expected with
      | .ok value => pure value
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [[value]] do
      fail s!"text function {expression}: wrong typed result"

def expectSQLiteRowExpressions : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n NUMERIC); INSERT INTO t VALUES(1,'abc','2'),(2,NULL,NULL);"
  let sql := setup ++ "SELECT t.id+1,upper(t.v),n='2',+n='2',CASE n WHEN '2' THEN 'yes' ELSE 'no' END FROM t ORDER BY id;"
  let (_, results) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"row expression: {message}"
  let expected : List (List Value) := [
    [.integer 2, .text "ABC", .integer 1, .integer 0, .text "yes"],
    [.integer 3, .null, .null, .null, .text "no"]]
  let expected ← match expected.mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (results.getLast?).map (·.rows) == some expected do
    fail "row expression value or column affinity changed"
  for query in ["SELECT missing+1 FROM t LIMIT 0;", "SELECT coalesce(1,missing) FROM t;",
      "SELECT wrong.id+1 FROM t;", "SELECT t.id+1 FROM t AS alias;"] do
    match CoreSQL.execute Core.State.empty (setup ++ query) with
    | .ok _ => fail s!"unbound row expression accepted: {query}"
    | .error _ => pure ()

def expectSQLiteRowUpdates : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,a INTEGER,b TEXT,n NOT NULL); INSERT INTO t VALUES(1,2,'3',1),(2,4,'5',2);"
  let (_, results) ← match CoreSQL.execute Core.State.empty
      (setup ++ "UPDATE t SET a=b,b=a,n=n+1 WHERE id+0; SELECT a,b,n FROM t ORDER BY id;") with
    | .ok outcome => pure outcome
    | .error message => fail s!"row UPDATE: {message}"
  let expected ← match [[Value.integer 3,.text "2",.integer 2],
      [.integer 5,.text "4",.integer 3]].mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (results.getLast?).map (·.rows) == some expected do fail "UPDATE RHS or affinity changed"
  unless (results.reverse[1]?).map (·.changes) == some 2 do fail "UPDATE change count changed"
  for query in ["UPDATE t SET a=missing WHERE 0;", "UPDATE t SET a=wrong.a;",
      "UPDATE t SET n=NULL WHERE id+0;", "UPDATE t SET a=abs(-9223372036854775808)+id;"] do
    match CoreSQL.execute Core.State.empty (setup ++ query) with
    | .ok _ => fail s!"invalid UPDATE accepted: {query}"
    | .error _ => pure ()
  let (_, duplicate) ← match CoreSQL.execute Core.State.empty
      (setup ++ "UPDATE t SET a=abs(-9223372036854775808),a=a+1; SELECT a FROM t ORDER BY id;") with
    | .ok outcome => pure outcome
    | .error message => fail s!"duplicate UPDATE: {message}"
  let expected ← match [[Value.integer 3],[.integer 5]].mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (duplicate.getLast?).map (·.rows) == some expected do fail "last UPDATE assignment did not win"

def expectIndexTailOwnership : IO Unit := do
  let .ok (state, _) := CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,2),(2,3); CREATE INDEX tv ON t(v);" |
    fail "index tail setup"
  let some table := state.database.findTable? "t" | fail "index tail table"
  let some index := table.indexes.head? | fail "index tail index"
  let some encoding := CoreOverflow.encodeIndex 2 table index | fail "index tail encoding"
  let source : CoreDecode.PageSource := {
    pageCount := 1 + encoding.pages.length
    readPage := fun number => if number < 2 then none else
      (encoding.pages[number - 2]?).map (·.bytes) }
  unless CoreFileAdapter.indexTailMatches source 2 encoding.pages do
    fail "exact canonical index tail rejected"
  if CoreFileAdapter.indexTailMatches { source with pageCount := source.pageCount + 1 }
      2 encoding.pages then fail "unaccounted tail page accepted"
  if CoreFileAdapter.indexTailMatches { source with readPage := fun _ => none }
      2 encoding.pages then fail "unreadable index tail accepted"

def expectSQLiteRowPredicates : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n NUMERIC); INSERT INTO t VALUES(1,'2','2'),(2,'x',NULL),(3,'3',-2);"
  for (query, expected) in [
      ("SELECT id FROM t WHERE id+1>2 ORDER BY id;", [2,3]),
      ("SELECT id FROM t WHERE v=CAST(2 AS INTEGER);", [1]),
      ("SELECT id FROM t WHERE coalesce(n,0);", [1,3]),
      ("SELECT id FROM t WHERE NOT (NULL AND id=2);", [1,3]),
      ("SELECT id FROM t WHERE NOT (NULL OR id=2);", []),
      ("SELECT id FROM t WHERE id+0 ORDER BY id DESC LIMIT 2;", [3,2]),
      ("SELECT id FROM t WHERE id+0 ORDER BY v DESC LIMIT 2;", [2,3]),
      ("SELECT id FROM t WHERE NULL AND abs(-9223372036854775808);", []),
      ("SELECT id FROM t WHERE id=1 OR abs(-9223372036854775808) LIMIT 1;", [1]),
      ("SELECT id FROM t WHERE abs(-9223372036854775808) LIMIT 0;", [])] do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ query) with
      | .ok outcome => pure outcome
      | .error message => fail s!"row predicate: {query}: {message}"
    let rows ← match expected.mapM (fun i => List.mapM SQLSurface.value [Value.integer i]) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do
      fail s!"row predicate result: {query}"
  for query in ["SELECT id FROM t WHERE abs(-9223372036854775808) AND 0;",
      "SELECT id FROM t WHERE id<0 AND abs(-9223372036854775808);",
      "SELECT 1 WHERE abs(-9223372036854775808) AND 0;",
      "SELECT id FROM t WHERE missing+1 LIMIT 0;",
      "SELECT id FROM t WHERE id=1 OR abs(-9223372036854775808);",
      "SELECT id FROM t WHERE wrong.id+1;",
      "SELECT missing FROM t WHERE 0;"] do
    match CoreSQL.execute Core.State.empty (setup ++ query) with
    | .ok _ => fail s!"invalid row predicate accepted: {query}"
    | .error _ => pure ()

end SQLeanite.Tests
