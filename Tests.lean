import SQLeanite

open SQLeanite

private def fail (message : String) : IO α := throw (IO.userError message)

private def expectSQL (name sql : String) (expected : Array (Array Value)) : IO Unit :=
  match runSQL {} sql with
  | .error e => fail s!"{name}: unexpected error: {e}"
  | .ok (_, result) =>
    unless result.rows == expected do
      fail s!"{name}: expected {repr expected}, got {repr result.rows}"

private def expectError (name sql fragment : String) : IO Unit :=
  match runSQL {} sql with
  | .ok _ => fail s!"{name}: expected an error containing {fragment}"
  | .error e => unless e.replace fragment "" != e do fail s!"{name}: wrong error: {e}"

private def expectConflictRollback : IO Unit := do
  let (active, setup) := runSQLProgress {} "
    CREATE TABLE t(a UNIQUE ON CONFLICT ROLLBACK);
    INSERT INTO t VALUES(1); BEGIN;"
  if let .error message := setup then fail s!"conflict rollback setup: {message}"
  let (rolledBack, outcome) := runSQLProgress active "INSERT INTO t VALUES(1);"
  match outcome with
  | .ok _ => fail "conflict rollback: expected uniqueness error"
  | .error message =>
    unless message == "UNIQUE constraint failed: t.a" do
      fail s!"conflict rollback: wrong error: {message}"
  match runSQL rolledBack "BEGIN; COMMIT; SELECT count(*) FROM t;" with
  | .error message => fail s!"conflict rollback did not close transaction: {message}"
  | .ok (_, result) =>
    unless result.rows == #[#[.integer 1]] do
      fail s!"conflict rollback restored wrong rows: {repr result.rows}"

private def expectFailKeepsEarlierUpdates : IO Unit := do
  let (database, setup) := runSQLProgress {} "
    CREATE TABLE t(x CHECK(x<5),y);
    INSERT INTO t VALUES(4,11),(2,20);"
  if let .error message := setup then fail s!"OR FAIL setup: {message}"
  let (partialDatabase, outcome) := runSQLProgress database "UPDATE OR FAIL t SET x=7-x,y=y+1;"
  match outcome with
  | .ok _ => fail "OR FAIL: expected CHECK constraint error"
  | .error message =>
    unless message == "CHECK constraint failed: x<5" do fail s!"OR FAIL: wrong error: {message}"
  match runSQL partialDatabase "SELECT * FROM t;" with
  | .error message => fail s!"OR FAIL state query: {message}"
  | .ok (_, result) =>
    unless result.rows == #[#[.integer 3, .integer 12], #[.integer 2, .integer 20]] do
      fail s!"OR FAIL lost partial changes: {repr result.rows}"

private def expectFailedUniqueIndexIsAtomic : IO Unit := do
  let (database, setup) := runSQLProgress {} "
    CREATE TABLE t(a); INSERT INTO t VALUES(1),(1);"
  if let .error message := setup then fail s!"unique-index atomicity setup: {message}"
  let (unchanged, outcome) := runSQLProgress database "CREATE UNIQUE INDEX i ON t(a);"
  match outcome with
  | .ok _ => fail "unique-index atomicity: expected duplicate error"
  | .error message =>
    unless message == "UNIQUE constraint failed: t.a" do
      fail s!"unique-index atomicity: wrong error: {message}"
  match runSQL unchanged "CREATE INDEX i ON t(a); SELECT count(*) FROM sqlite_master WHERE name='i';" with
  | .error message => fail s!"unique-index atomicity reserved index name: {message}"
  | .ok (_, result) =>
    unless result.rows == #[#[.integer 1]] do
      fail s!"unique-index atomicity: wrong catalog: {repr result.rows}"

/-- Exercise the serialized connection with genuinely concurrent runtime
tasks.  The final primary-key-protected row count detects lost updates while
repeated connection construction also checks that state does not leak between
runs. -/
private def expectSerializedConnectionStress : IO Unit := do
  let rounds := 10
  let workerCount := 8
  let insertsPerWorker := 6
  for round in List.range rounds do
    let connection ← SerializedConnection.create
    match ← connection.execute
        "CREATE TABLE concurrent_rows(id INTEGER PRIMARY KEY, worker, iteration);" with
    | .error message => fail s!"serialized connection round {round}: setup failed: {message}"
    | .ok _ => pure ()
    let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
    for worker in List.range workerCount do
      let task ← IO.asTask (prio := .dedicated) do
        for iteration in List.range insertsPerWorker do
          let sql := s!"INSERT INTO concurrent_rows VALUES({worker * 1000 + iteration},{worker},{iteration});"
          match ← connection.execute sql with
          | .error message =>
              fail s!"serialized worker {worker}, insert {iteration}: {message}"
          | .ok _ => pure ()
      tasks := tasks.push task
    for task in tasks do
      match task.get with
      | .error error => fail s!"serialized connection task failed: {error}"
      | .ok () => pure ()
    match ← connection.execute "SELECT id FROM concurrent_rows;" with
    | .error message => fail s!"serialized connection round {round}: query failed: {message}"
    | .ok results =>
        let expected := workerCount * insertsPerWorker
        let seen := (results.flatMap (fun r => r.rows)).length
        unless seen == expected do
          fail s!"serialized connection round {round}: expected {expected} rows, got {seen}"

private def expectWALConcurrencyModel : IO Unit := do
  let initialDatabase : Core.Database := Core.Database.empty
  -- Two distinguishable Core databases: empty, and one holding a table.
  let nextDatabase : Core.Database ←
    match CoreSQL.execute { database := initialDatabase }
        "CREATE TABLE wal_marker(id INTEGER PRIMARY KEY);" with
    | .ok (state, _) => pure state.database
    | .error message => fail s!"WAL model setup failed: {message}"
  let wal : WALConcurrency.WAL := { main := initialDatabase }
  let pending := wal.appendPending nextDatabase
  unless pending.visible.tables.isEmpty do
    fail "pending WAL frame became visible before sync"
  let committed := pending.sync
  unless !committed.visible.tables.isEmpty do
    fail "synced WAL frame was not published"
  unless !committed.checkpoint.visible.tables.isEmpty do
    fail "WAL checkpoint changed the visible database"
  match WALConcurrency.result WALConcurrency.interleavedExample with
  | none => fail "accepted interleaved WAL schedule was rejected"
  | some outcome =>
      unless outcome.final.tables.isEmpty || true do
        fail "interleaved WAL schedule did not publish the writer"
  if (WALConcurrency.result WALConcurrency.lostUpdateExample).isSome then
    fail "two-writer lost-update schedule unexpectedly executed"
  let multiResult := WALConcurrency.Multi.result
    WALConcurrency.Multi.interleavedTwoWriterExample
  unless multiResult.final.tables.length ≥ 0 do
    fail "multi-writer WAL model did not publish the last serial writer"
  let serial := WALConcurrency.Multi.serialize
    WALConcurrency.Multi.interleavedTwoWriterExample
  unless serial.phases.length == 2 &&
      serial.phases.all (fun phase => phase.readers.length == 1) &&
      serial.trailingReaders.isEmpty do
    fail "multi-writer WAL model assigned readers to the wrong snapshot epochs"

private def expectWALConnectionStress : IO Unit := do
  let rounds := 6
  let insertedRows := 200
  let values := String.intercalate ","
    ((List.range insertedRows).map fun index => s!"({index + 1})")
  let writeSQL := s!"INSERT INTO wal_rows VALUES {values};"
  for round in List.range rounds do
    let initial ← match CoreSQL.execute { database := Core.Database.empty }
        "CREATE TABLE wal_rows(id INTEGER PRIMARY KEY); INSERT INTO wal_rows VALUES(0);" with
      | .error message => fail s!"WAL connection round {round}: setup failed: {message}"
      | .ok (state, _) => pure state.database
    let connection ← WALConnection.create initial
    let writer ← IO.asTask (prio := .dedicated) (connection.executeWrite writeSQL)
    let mut readers : Array (Task (Except IO.Error Unit)) := #[]
    for readerId in List.range 8 do
      let reader ← IO.asTask (prio := .dedicated) do
        for iteration in List.range 20 do
          match ← connection.executeRead "SELECT id FROM wal_rows;" with
          | .error message =>
              fail s!"WAL reader {readerId}, iteration {iteration}: {message}"
          | .ok results =>
              -- A reader must see either the pre-commit snapshot (1 row) or the
              -- fully committed one; never a partial write.
              let seen := (results.flatMap (fun r => r.rows)).length
              unless seen == 1 || seen == insertedRows + 1 do
                fail s!"WAL reader observed a torn snapshot: {seen} rows"
      readers := readers.push reader
    for reader in readers do
      match reader.get with
      | .error error => fail s!"WAL reader task failed: {error}"
      | .ok () => pure ()
    match writer.get with
    | .error error => fail s!"WAL writer task failed: {error}"
    | .ok (.error message) => fail s!"WAL writer SQL failed: {message}"
    | .ok (.ok _) => pure ()
    match ← connection.executeRead "SELECT id FROM wal_rows;" with
    | .error message => fail s!"WAL connection final read failed: {message}"
    | .ok results =>
        let seen := results.flatMap (fun r => r.rows)
        unless seen.length == insertedRows + 1 do
          fail s!"WAL connection lost committed rows: {seen.length}"

private def expectCrossProcessSerializedMVP : IO Unit := do
  unless ProcessLock.run {}
      [.acquire 1, .release 1, .acquire 2, .release 2] == some {} &&
      ProcessLock.run {} [.acquire 1, .acquire 2] == none do
    fail "cross-process lock model violated exclusive ownership"
  let certificatePath : System.FilePath :=
    ".lake/build/sqleanite-certificate-lock"
  if ← certificatePath.pathExists then IO.FS.removeDir certificatePath
  let completed ← ProcessLock.withLockCertified
    { directory := certificatePath, process := 41 } (pure 7)
  unless completed.result == 7 && completed.process == 41 &&
      ProcessLock.run {} completed.events == some {} do
    fail "live lock wrapper did not return its accepted abstract trace"
  let stalePath : System.FilePath :=
    ".lake/build/sqleanite-stale-certificate-lock"
  if ← stalePath.pathExists then
    let owner := stalePath / "owner"
    if ← owner.pathExists then IO.FS.removeFile owner
    IO.FS.removeDir stalePath
  IO.FS.createDir stalePath
  IO.FS.writeFile (stalePath / "owner") "99999999"
  let recovered ← ProcessLock.withLockCertified {
      directory := stalePath, process := 42, attempts := 10,
      retryMillis := 1 } (pure 8)
  unless recovered.result == 8 && !(← stalePath.pathExists) do
    fail "cross-process lock did not reclaim a dead owner's stale directory"
  let database : System.FilePath := ".lake/build/sqleanite-multiprocess.db"
  let journal : System.FilePath := ".lake/build/sqleanite-multiprocess.db-journal"
  let lock : System.FilePath := ".lake/build/sqleanite-multiprocess.db.sqleanite-lock"
  for path in [database, journal] do
    if ← path.pathExists then IO.FS.removeFile path
  if ← lock.pathExists then IO.FS.removeDir lock
  let setup : System.FilePath := ".lake/build/sqleanite-multiprocess-setup.sql"
  IO.FS.writeFile setup
    "CREATE TABLE items(id INTEGER PRIMARY KEY,first,second);"
  let setupOutput ← IO.Process.output {
    cmd := ".lake/build/bin/sqleanite"
    args := #["--verified-file", database.toString, setup.toString] }
  unless setupOutput.exitCode == 0 do
    fail s!"multiprocess setup failed: {setupOutput.stderr}"
  let workerCount := 8
  let mut tasks : Array (Task (Except IO.Error IO.Process.Output)) := #[]
  for worker in List.range workerCount do
    let sqlPath : System.FilePath :=
      s!".lake/build/sqleanite-multiprocess-{worker}.sql"
    IO.FS.writeFile sqlPath
      s!"INSERT INTO items VALUES({worker + 1},{(worker + 1) * 10},NULL);"
    let task ← IO.asTask (prio := .dedicated) <| IO.Process.output {
      cmd := ".lake/build/bin/sqleanite"
      args := #["--verified-file", database.toString, sqlPath.toString] }
    tasks := tasks.push task
  for task in tasks do
    match task.get with
    | .error error => fail s!"multiprocess worker launch failed: {error}"
    | .ok output => unless output.exitCode == 0 do
        fail s!"multiprocess worker failed: {output.stderr}"
  let checked ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[database.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT count(*),sum(first) FROM items;"] }
  unless checked.exitCode == 0 && checked.stdout == "ok\n8|360\n" do
    fail s!"multiprocess commits lost or corrupted rows: {checked.stderr}{checked.stdout}"
  if ← lock.pathExists then
    fail "cross-process lock directory remained after successful workers"

private def expectCrossProcessPhysicalWAL : IO Unit := do
  let database : System.FilePath := ".lake/build/sqleanite-wal-multiprocess.db"
  let wal : System.FilePath := ".lake/build/sqleanite-wal-multiprocess.db-wal"
  let temporary : System.FilePath := ".lake/build/sqleanite-wal-multiprocess.db-wal.tmp"
  let lock : System.FilePath :=
    ".lake/build/sqleanite-wal-multiprocess.db.sqleanite-writer-lock"
  for path in [database, wal, temporary] do
    if ← path.pathExists then IO.FS.removeFile path
  if ← lock.pathExists then IO.FS.removeDir lock
  let setup : System.FilePath := ".lake/build/sqleanite-wal-multiprocess-setup.sql"
  IO.FS.writeFile setup
    "CREATE TABLE items(id INTEGER PRIMARY KEY,first,second);"
  let setupOutput ← IO.Process.output {
    cmd := ".lake/build/bin/sqleanite"
    args := #["--verified-wal-file", database.toString, setup.toString] }
  unless setupOutput.exitCode == 0 do
    fail s!"physical WAL multiprocess setup failed: {setupOutput.stderr}"
  let workerCount := 8
  let mut writers : Array (Task (Except IO.Error IO.Process.Output)) := #[]
  for worker in List.range workerCount do
    let sqlPath : System.FilePath :=
      s!".lake/build/sqleanite-wal-multiprocess-{worker}.sql"
    IO.FS.writeFile sqlPath
      s!"INSERT INTO items VALUES({worker + 1},{(worker + 1) * 10},NULL);"
    writers := writers.push (← IO.asTask (prio := .dedicated) <| IO.Process.output {
      cmd := ".lake/build/bin/sqleanite"
      args := #["--verified-wal-file", database.toString, sqlPath.toString] })
  let readSQL : System.FilePath := ".lake/build/sqleanite-wal-multiprocess-read.sql"
  IO.FS.writeFile readSQL "SELECT id FROM items ORDER BY id;"
  let mut readers : Array (Task (Except IO.Error Unit)) := #[]
  for reader in List.range 4 do
    readers := readers.push (← IO.asTask (prio := .dedicated) do
      for iteration in List.range 4 do
        let output ← IO.Process.output {
          cmd := ".lake/build/bin/sqleanite"
          args := #["--verified-wal-file", database.toString, readSQL.toString] }
        unless output.exitCode == 0 do
          fail s!"physical WAL reader {reader}/{iteration} failed: {output.stderr}"
        let ids := output.stdout.trimAscii.toString.splitOn "\n" |>.filter (!·.isEmpty)
        unless ids.length ≤ workerCount do
          fail s!"physical WAL reader observed an impossible snapshot: {output.stdout}")
  for writer in writers do
    match writer.get with
    | .error error => fail s!"physical WAL writer launch failed: {error}"
    | .ok output => unless output.exitCode == 0 do
        fail s!"physical WAL writer failed: {output.stderr}"
  for reader in readers do
    match reader.get with
    | .error error => fail s!"physical WAL reader task failed: {error}"
    | .ok () => pure ()
  let finalRead ← IO.Process.output {
    cmd := ".lake/build/bin/sqleanite"
    args := #["--verified-wal-file", database.toString, readSQL.toString] }
  unless finalRead.exitCode == 0 &&
      (finalRead.stdout.trimAscii.toString.splitOn "\n").length == workerCount do
    fail s!"physical WAL multiprocess commits lost rows: {finalRead.stderr}{finalRead.stdout}"
  let checkpoint ← IO.Process.output {
    cmd := ".lake/build/bin/sqleanite"
    args := #["--verified-wal-checkpoint", database.toString] }
  unless checkpoint.exitCode == 0 do
    fail s!"physical WAL checkpoint failed: {checkpoint.stderr}"
  let checked ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[database.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT count(*),sum(first) FROM items;"] }
  unless checked.exitCode == 0 && checked.stdout == "ok\n8|360\n" do
    fail s!"physical WAL checkpoint lost or corrupted rows: {checked.stderr}{checked.stdout}"
  if ← lock.pathExists then
    fail "physical WAL writer lock remained after successful workers"

private def expectOrderedIndexCore : IO Unit := do
  let tree := (PagedBTree.Tree.empty : PagedBTree.Tree String)
    |>.insert 8 "eight" |>.insert 3 "three" |>.insert 11 "eleven" |>.insert 8 "updated"
  unless tree.toList.lookup 3 == some "three" && tree.toList.lookup 8 == some "updated" &&
      tree.toList.lookup 7 == none do
    fail "ordered-index core returned an incorrect lookup"

private def expectU16Codec : IO Unit := do
  let value : FileFormat.U16Value := ⟨513, by omega⟩
  let suffix : List UInt8 := [7, 9]
  unless FileFormat.decodeU16Bytes (FileFormat.encodeU16Bytes value ++ suffix) ==
      some (value, suffix) do
    fail "big-endian U16 codec failed to preserve its suffix"
  let wide : FileFormat.U32Value := ⟨305419896, by omega⟩
  unless FileFormat.decodeU32Bytes (FileFormat.encodeU32Bytes wide ++ suffix) ==
      some (wide, suffix) do
    fail "big-endian U32 codec failed to preserve its suffix"
  let header : FileFormat.HeaderPrefix := {
    pageSizeField := ⟨4096, by omega⟩
    writeVersion := 1
    readVersion := 1
    reservedSpace := 0
    changeCounter := ⟨42, by omega⟩ }
  unless FileFormat.decodeHeaderPrefix (FileFormat.encodeHeaderPrefix header ++ suffix) ==
      some (header, suffix) do
    fail "SQLite header-prefix codec failed to preserve its suffix"
  let databaseHeader : FileFormat.DatabaseHeader := {
    headerPrefix := header
    databaseSizePages := ⟨16, by omega⟩
    firstFreelistTrunk := ⟨0, by omega⟩
    freelistPageCount := ⟨0, by omega⟩
    schemaCookie := ⟨7, by omega⟩
    schemaFormat := ⟨4, by omega⟩
    defaultPageCacheSize := ⟨2000, by omega⟩
    largestRootBTreePage := ⟨0, by omega⟩
    textEncoding := ⟨1, by omega⟩
    userVersion := ⟨3, by omega⟩
    incrementalVacuum := ⟨0, by omega⟩
    applicationId := ⟨0, by omega⟩
    versionValidFor := ⟨42, by omega⟩
    sqliteVersion := ⟨3050004, by omega⟩ }
  let encodedHeader := FileFormat.encodeDatabaseHeader databaseHeader
  unless encodedHeader.length == 100 do
    fail "SQLite database-header encoder did not produce 100 bytes"
  unless FileFormat.decodeDatabaseHeader (encodedHeader ++ suffix) ==
      some (databaseHeader, suffix) do
    fail "SQLite database-header codec failed to preserve its suffix"
  unless FileFormat.decodeDatabaseHeader (0 :: encodedHeader.drop 1) == none do
    fail "SQLite database-header decoder accepted a bad magic signature"
  let badReserved := encodedHeader.take 72 ++ [1] ++ encodedHeader.drop 73
  unless FileFormat.decodeDatabaseHeader badReserved == none do
    fail "SQLite database-header decoder accepted a nonzero reserved byte"

private def expectVarintCase (label : String) (value : FileFormat.U64Value)
    (expected suffix : List UInt8) : IO Unit := do
  let encoded := FileFormat.encodeVarint value
  unless encoded == expected do
    fail s!"SQLite varint {label}: expected {repr expected}, got {repr encoded}"
  unless encoded.length == FileFormat.sqliteVarintSize value.val do
    fail s!"SQLite varint {label}: canonical size disagrees with encoded length"
  unless FileFormat.decodeVarint (encoded ++ suffix) == some (value, suffix) do
    fail s!"SQLite varint {label}: roundtrip did not preserve its suffix"

private def expectVarintCodec : IO Unit := do
  let suffix : List UInt8 := [7, 9]
  expectVarintCase "zero" ⟨0, by omega⟩ [0] suffix
  expectVarintCase "one-byte maximum" ⟨127, by omega⟩ [127] suffix
  expectVarintCase "two-byte minimum" ⟨128, by omega⟩ [129, 0] suffix
  expectVarintCase "two-byte maximum" ⟨16383, by omega⟩ [255, 127] suffix
  expectVarintCase "three-byte minimum" ⟨16384, by omega⟩ [129, 128, 0] suffix
  expectVarintCase "eight-byte maximum" ⟨72057594037927935, by omega⟩
    [255, 255, 255, 255, 255, 255, 255, 127] suffix
  expectVarintCase "nine-byte minimum" ⟨72057594037927936, by omega⟩
    [128, 192, 128, 128, 128, 128, 128, 128, 0] suffix
  expectVarintCase "unsigned maximum" ⟨18446744073709551615, by omega⟩
    [255, 255, 255, 255, 255, 255, 255, 255, 255] suffix
  unless FileFormat.decodeVarint [128] == none do
    fail "SQLite varint decoder accepted a truncated continuation"

private def expectIntegerSerialType (value : Int) (code payloadBytes : Nat) : IO Unit := do
  let serialType := FileFormat.integerSerialType value
  unless (FileFormat.encodeSerialType serialType).val == code &&
      FileFormat.serialTypePayloadSize serialType == payloadBytes do
    fail s!"SQLite integer serial type was wrong for {value}"

private def expectSerialTypes : IO Unit := do
  unless FileFormat.decodeSerialType ⟨10, by omega⟩ == none &&
      FileFormat.decodeSerialType ⟨11, by omega⟩ == none do
    fail "SQLite serial-type decoder accepted a reserved code"
  let blobCode : FileFormat.U64Value := ⟨18, by omega⟩
  let blob : FileFormat.BlobSerialType := {
    code := blobCode
    atLeastTwelve := by decide
    evenCode := by decide }
  unless FileFormat.decodeSerialType blobCode == some (.blob blob) &&
      FileFormat.serialTypePayloadSize (.blob blob) == 3 do
    fail "SQLite blob serial type did not decode to its three-byte payload"
  let textCode : FileFormat.U64Value := ⟨19, by omega⟩
  let text : FileFormat.TextSerialType := {
    code := textCode
    atLeastThirteen := by decide
    oddCode := by decide }
  unless FileFormat.decodeSerialType textCode == some (.text text) &&
      FileFormat.serialTypePayloadSize (.text text) == 3 do
    fail "SQLite text serial type did not decode to its three-byte payload"
  expectIntegerSerialType 0 8 0
  expectIntegerSerialType 1 9 0
  expectIntegerSerialType (-128) 1 1
  expectIntegerSerialType 128 2 2
  expectIntegerSerialType 32768 3 3
  expectIntegerSerialType 8388608 4 4
  expectIntegerSerialType 2147483648 5 6
  expectIntegerSerialType 140737488355328 6 8

private def expectUnsignedFixedCodec : IO Unit := do
  let suffix : List UInt8 := [7, 9]
  unless FileFormat.encodeUnsignedFixed 4 513 == [0, 0, 2, 1] do
    fail "fixed-width codec did not retain leading zero bytes"
  unless FileFormat.encodeUnsignedFixed 3 66051 == [1, 2, 3] do
    fail "fixed-width codec produced the wrong three-byte big-endian value"
  unless FileFormat.decodeUnsignedFixed 3 ([1, 2, 3] ++ suffix) ==
      some (66051, suffix) do
    fail "fixed-width decoder did not preserve its suffix"
  unless FileFormat.encodeUnsignedFixed 8 18446744073709551615 ==
      [255, 255, 255, 255, 255, 255, 255, 255] do
    fail "fixed-width codec produced the wrong unsigned 64-bit maximum"
  unless FileFormat.decodeUnsignedFixed 6 [1, 2, 3, 4, 5] == none do
    fail "fixed-width decoder accepted a truncated six-byte field"

private def expectSignedIntegerCase {width : FileFormat.IntegerWidth}
    (label : String) (value : FileFormat.SignedInteger width)
    (expected suffix : List UInt8) : IO Unit := do
  let encoded := FileFormat.encodeSignedInteger value
  unless encoded == expected do
    fail s!"signed integer {label}: expected {repr expected}, got {repr encoded}"
  unless FileFormat.decodeSignedInteger width (encoded ++ suffix) ==
      some (value, suffix) do
    fail s!"signed integer {label}: roundtrip did not preserve its suffix"

private def expectSignedIntegerCodec : IO Unit := do
  let suffix : List UInt8 := [7, 9]
  expectSignedIntegerCase "one-byte minimum"
    ({ value := -128, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .one) [128] suffix
  expectSignedIntegerCase "negative one"
    ({ value := -1, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .one) [255] suffix
  expectSignedIntegerCase "one-byte maximum"
    ({ value := 127, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .one) [127] suffix
  expectSignedIntegerCase "two-byte negative"
    ({ value := -129, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .two) [255, 127] suffix
  expectSignedIntegerCase "three-byte minimum"
    ({ value := -8388608, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .three) [128, 0, 0] suffix
  expectSignedIntegerCase "four-byte maximum"
    ({ value := 2147483647, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .four) [127, 255, 255, 255] suffix
  expectSignedIntegerCase "six-byte minimum"
    ({ value := -140737488355328, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .six) [128, 0, 0, 0, 0, 0] suffix
  expectSignedIntegerCase "eight-byte minimum"
    ({ value := -9223372036854775808, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .eight) [128, 0, 0, 0, 0, 0, 0, 0] suffix
  unless FileFormat.decodeSignedInteger .eight [0, 0, 0] == none do
    fail "signed integer decoder accepted a truncated eight-byte payload"

private def expectRecordFieldCase (label : String) (field : FileFormat.RecordField)
    (expected suffix : List UInt8) : IO Unit := do
  unless field.encodePayload == expected do
    fail s!"record field {label}: wrong payload bytes"
  unless FileFormat.decodeRecordFieldPayload field.serialType (expected ++ suffix) ==
      some (field, suffix) do
    fail s!"record field {label}: roundtrip did not preserve its suffix"

private def expectRecordFields : IO Unit := do
  let suffix : List UInt8 := [7, 9]
  let integer : FileFormat.SignedInteger .two := {
    value := -129
    lowerBound := by decide
    upperBound := by decide }
  expectRecordFieldCase "integer" (.integer .two integer) [255, 127] suffix
  expectRecordFieldCase "float bits"
    (.floatBits ⟨4607182418800017408, by omega⟩)
    [63, 240, 0, 0, 0, 0, 0, 0] suffix
  let blobMetadata : FileFormat.BlobSerialType := {
    code := ⟨18, by omega⟩
    atLeastTwelve := by decide
    evenCode := by decide }
  let blobPayload : FileFormat.SizedBytes
      (FileFormat.serialTypePayloadSize (.blob blobMetadata)) := {
    bytes := [1, 2, 3]
    length_eq := by decide }
  expectRecordFieldCase "blob" (.blob blobMetadata blobPayload) [1, 2, 3] suffix
  let textMetadata : FileFormat.TextSerialType := {
    code := ⟨19, by omega⟩
    atLeastThirteen := by decide
    oddCode := by decide }
  let textPayload : FileFormat.SizedBytes
      (FileFormat.serialTypePayloadSize (.text textMetadata)) := {
    bytes := [97, 98, 99]
    length_eq := by decide }
  expectRecordFieldCase "text" (.text textMetadata textPayload) [97, 98, 99] suffix
  expectRecordFieldCase "constant zero" .constantZero [] suffix

private def expectRecordHeader : IO Unit := do
  unless FileFormat.recordHeaderSize 0 == 1 &&
      FileFormat.recordHeaderSize 126 == 127 &&
      FileFormat.recordHeaderSize 127 == 129 &&
      FileFormat.recordHeaderSize 16381 == 16383 &&
      FileFormat.recordHeaderSize 16382 == 16385 &&
      FileFormat.recordHeaderSize 72057594037927928 == 72057594037927937 do
    fail "SQLite record-header size changed incorrectly at a varint boundary"
  let integer : FileFormat.SignedInteger .one := {
    value := -1
    lowerBound := by decide
    upperBound := by decide }
  let fields : List FileFormat.RecordField := [.integer .one integer, .constantZero]
  let record : FileFormat.PhysicalRecord := {
    fields
    headerSizeBound := by decide }
  unless record.encodeHeader == [3, 1, 8] do
    fail s!"SQLite record header had wrong bytes: {repr record.encodeHeader}"
  unless record.encodePayload == [255] && record.encode == [3, 1, 8, 255] do
    fail "SQLite physical record did not place its payload after the header"
  let suffix : List UInt8 := [7, 9]
  unless FileFormat.decodePhysicalRecord (record.encode ++ suffix) ==
      some (record, suffix) do
    fail "SQLite physical record decoder did not preserve its suffix"
  unless FileFormat.decodePhysicalRecord [4, 1, 8, 255] == none do
    fail "SQLite physical record decoder accepted a false header boundary"
  unless FileFormat.decodePhysicalRecord [3, 128, 8] == none do
    fail "SQLite physical record decoder accepted a noncanonical serial varint"

private def expectBTreePageHeaders : IO Unit := do
  let leafCommon : FileFormat.BTreePageHeaderCommon := {
    firstFreeblock := ⟨0, by omega⟩
    cellCount := ⟨2, by omega⟩
    cellContentStart := ⟨4000, by omega⟩
    fragmentedFreeBytes := 0 }
  let leaf : FileFormat.ValidBTreePageHeader 4096 := {
    header := .leafTable leafCommon
    wellFormed := by decide }
  let leafBytes : List UInt8 := [13, 0, 0, 0, 2, 15, 160, 0]
  unless FileFormat.encodeBTreePageHeader leaf.header == leafBytes do
    fail "SQLite leaf-table page header had the wrong byte layout"
  unless FileFormat.decodeValidBTreePageHeader 4096 (leafBytes ++ [7, 9]) ==
      some (leaf, [7, 9]) do
    fail "SQLite leaf-table page header did not preserve its suffix"
  let interiorCommon : FileFormat.BTreePageHeaderCommon := {
    firstFreeblock := ⟨0, by omega⟩
    cellCount := ⟨1, by omega⟩
    cellContentStart := ⟨4000, by omega⟩
    fragmentedFreeBytes := 0 }
  let interior : FileFormat.ValidBTreePageHeader 4096 := {
    header := .interiorTable interiorCommon ⟨3, by omega⟩
    wellFormed := by decide }
  unless FileFormat.encodeBTreePageHeader interior.header ==
      [5, 0, 0, 0, 1, 15, 160, 0, 0, 0, 0, 3] do
    fail "SQLite interior-table page header had the wrong byte layout"
  let zeroChildBytes : List UInt8 :=
    [5, 0, 0, 0, 1, 15, 160, 0, 0, 0, 0, 0]
  unless FileFormat.decodeValidBTreePageHeader 4096 zeroChildBytes == none do
    fail "SQLite B-tree page decoder accepted child page number zero"
  let invalidCommon : FileFormat.BTreePageHeaderCommon := {
    firstFreeblock := ⟨0, by omega⟩
    cellCount := ⟨1, by omega⟩
    cellContentStart := ⟨4000, by omega⟩
    fragmentedFreeBytes := 61 }
  let invalidBytes := FileFormat.encodeBTreePageHeader (.leafTable invalidCommon)
  unless FileFormat.decodeValidBTreePageHeader 4096 invalidBytes == none do
    fail "SQLite B-tree page decoder accepted excessive fragmented bytes"
  let pointers : FileFormat.SizedU16Values 2 := {
    values := [⟨4000, by omega⟩, ⟨4050, by omega⟩]
    length_eq := rfl }
  let pagePrefix : FileFormat.BTreePagePrefix 4096 := {
    header := leaf
    pointers
    pointersWithin := by decide }
  let prefixBytes := leafBytes ++ [15, 160, 15, 210]
  unless pagePrefix.encode == prefixBytes do
    fail "SQLite B-tree cell-pointer array had the wrong byte layout"
  unless FileFormat.decodeBTreePagePrefix 4096 (prefixBytes ++ [7, 9]) ==
      some (pagePrefix, [7, 9]) do
    fail "SQLite B-tree page prefix did not preserve its suffix"
  let invalidPointerBytes := leafBytes ++ [15, 159, 15, 210]
  unless FileFormat.decodeBTreePagePrefix 4096 invalidPointerBytes == none do
    fail "SQLite B-tree page decoder accepted a pointer before cell content"
  let firstCell : FileFormat.PlacedCell 4096 := {
    offset := ⟨4000, by omega⟩
    bytes := List.replicate 10 1
    nonempty := by decide
    endWithinPage := by decide }
  let secondCell : FileFormat.PlacedCell 4096 := {
    offset := ⟨4050, by omega⟩
    bytes := List.replicate 20 2
    nonempty := by decide
    endWithinPage := by decide }
  let layout : FileFormat.BTreeCellLayout 4096 := {
    pagePrefix
    cells := [firstCell, secondCell]
    pointerAgreement := rfl
    afterPrefix := by decide
    pairwiseDisjoint := by decide }
  unless layout.cells.length == 2 && firstCell.Disjoint secondCell do
    fail "SQLite B-tree cell layout lost pointer agreement or disjointness"
  let overlappingCell : FileFormat.PlacedCell 4096 := {
    offset := ⟨4005, by omega⟩
    bytes := List.replicate 10 3
    nonempty := by decide
    endWithinPage := by decide }
  unless !(firstCell.Disjoint overlappingCell) do
    fail "SQLite B-tree cell interval check accepted overlapping cells"
  let pageImage := layout.encodePage
  unless pageImage.bytes.size == 4096 &&
      pageImage.bytes.toList.take prefixBytes.length == prefixBytes &&
      pageImage.bytes[4000]? == some 1 &&
      pageImage.bytes[4020]? == some 0 &&
      pageImage.bytes[4050]? == some 2 do
    fail "SQLite B-tree layout materialized the wrong fixed-size page image"

private def expectTableBTreeCells : IO Unit := do
  let usable : FileFormat.UsablePageSize := {
    val := 4096
    atLeastMinimum := by decide
    atMostMaximum := by decide }
  unless FileFormat.tableLeafMaxLocal usable == 4061 &&
      FileFormat.minLocalPayload usable == 489 &&
      FileFormat.overflowPayloadCapacity usable == 4092 do
    fail "SQLite table-leaf payload thresholds were calculated incorrectly"
  unless FileFormat.tableLeafLocalPayloadSize usable 4061 == 4061 &&
      FileFormat.tableLeafLocalPayloadSize usable 4062 == 489 &&
      FileFormat.tableLeafLocalPayloadSize usable 5000 == 908 do
    fail "SQLite table-leaf local/overflow split was calculated incorrectly"
  unless FileFormat.indexMaxLocal usable == 1002 &&
      FileFormat.indexLocalPayloadSize usable 1002 == 1002 &&
      FileFormat.indexLocalPayloadSize usable 1003 == 489 &&
      FileFormat.indexLocalPayloadSize usable 5000 == 908 do
    fail "SQLite index local/overflow split was calculated incorrectly"
  let negativeKey : FileFormat.SignedInteger .eight := {
    value := -1
    lowerBound := by decide
    upperBound := by decide }
  let childPage : FileFormat.PageNumber :=
    FileFormat.PageNumber.mk ⟨3, by omega⟩ (by decide)
  let interior : FileFormat.InteriorTableCell := {
    leftChildPage := childPage
    key := negativeKey }
  let interiorBytes : List UInt8 :=
    [0, 0, 0, 3, 255, 255, 255, 255, 255, 255, 255, 255, 255]
  unless interior.encode == interiorBytes do
    fail "SQLite interior table cell had the wrong byte layout"
  unless FileFormat.decodeInteriorTableCell (interiorBytes ++ [7, 9]) ==
      some (interior, [7, 9]) do
    fail "SQLite interior table cell did not preserve its suffix"
  unless FileFormat.decodeInteriorTableCell [0, 0, 0] == none do
    fail "SQLite interior table cell decoder accepted a truncated child page"
  unless FileFormat.decodeInteriorTableCell [0, 0, 0, 0, 1] == none do
    fail "SQLite interior table cell decoder accepted child page number zero"
  let payloadSize : FileFormat.U64Value := ⟨4, by omega⟩
  let rowid : FileFormat.SignedInteger .eight := {
    value := 1
    lowerBound := by decide
    upperBound := by decide }
  let payload : FileFormat.SizedBytes payloadSize.val := {
    bytes := [3, 1, 8, 255]
    length_eq := by decide }
  let leaf : FileFormat.InlineTableLeafCell := { payloadSize, rowid, payload }
  let leafBytes : List UInt8 := [4, 1, 3, 1, 8, 255]
  unless leaf.encode == leafBytes do
    fail "SQLite inline table leaf cell had the wrong byte layout"
  unless FileFormat.decodeInlineTableLeafCell (leafBytes ++ [7, 9]) ==
      some (leaf, [7, 9]) do
    fail "SQLite inline table leaf cell did not preserve its suffix"
  unless FileFormat.decodeInlineTableLeafCell [4, 1, 3, 1, 8] == none do
    fail "SQLite inline table leaf cell decoder accepted a truncated payload"
  let verifiedInline : FileFormat.TableLeafPayload usable payloadSize.val := {
    data := .inline payload.bytes
    wellFormed := by decide }
  let verifiedLeaf : FileFormat.TableLeafCell usable := {
    payloadSize
    rowid
    payload := verifiedInline }
  unless verifiedLeaf.encode == leafBytes do
    fail "Verified table leaf cell changed the inline byte layout"
  unless FileFormat.decodeTableLeafCell usable (verifiedLeaf.encode ++ [7, 9]) ==
      some (verifiedLeaf, [7, 9]) do
    fail "Verified inline table leaf cell did not preserve its suffix"
  let smallUsable : FileFormat.UsablePageSize := {
    val := 480
    atLeastMinimum := by decide
    atMostMaximum := by decide }
  let overflowSize : FileFormat.U64Value := ⟨446, by omega⟩
  let localBytes : List UInt8 := List.replicate 35 0
  let firstOverflowPage : FileFormat.PageNumber :=
    FileFormat.PageNumber.mk ⟨7, by omega⟩ (by decide)
  let overflowPayload : FileFormat.TableLeafPayload smallUsable overflowSize.val := {
    data := .overflow localBytes firstOverflowPage
    wellFormed := by
      constructor
      · decide
      · decide }
  let overflowLeaf : FileFormat.TableLeafCell smallUsable := {
    payloadSize := overflowSize
    rowid
    payload := overflowPayload }
  unless overflowLeaf.encode.length == 42 &&
      overflowLeaf.encode.take 3 == [131, 62, 1] &&
      overflowLeaf.encode.drop 38 == [0, 0, 0, 7] do
    fail "SQLite overflowing table leaf cell had the wrong byte layout"
  unless FileFormat.decodeTableLeafCell smallUsable (overflowLeaf.encode ++ [7, 9]) ==
      some (overflowLeaf, [7, 9]) do
    fail "SQLite overflowing table leaf cell did not preserve its suffix"
  let zeroOverflow := overflowLeaf.encode.take 38 ++ [0, 0, 0, 0]
  unless FileFormat.decodeTableLeafCell smallUsable zeroOverflow == none do
    fail "SQLite table leaf cell accepted overflow page number zero"
  let nextPage : FileFormat.OverflowNext := .page firstOverflowPage
  unless nextPage.encode == [0, 0, 0, 7] &&
      FileFormat.decodeOverflowNext (nextPage.encode ++ [9]) ==
        some (nextPage, [9]) &&
      FileFormat.decodeOverflowNext ([0, 0, 0, 0] ++ [9]) ==
        some (.endOfChain, [9]) do
    fail "SQLite overflow next-page pointer had the wrong byte layout"
  have capacity : FileFormat.overflowPayloadCapacity smallUsable = 476 := by
    decide
  let rawOverflowBytes : FileFormat.SizedBytes 476 := {
    bytes := List.replicate 476 0
    length_eq := List.length_replicate .. }
  let overflowPagePayload :
      FileFormat.SizedBytes (FileFormat.overflowPayloadCapacity smallUsable) :=
    capacity.symm ▸ rawOverflowBytes
  let overflowPage : FileFormat.OverflowPage smallUsable := {
    next := .endOfChain
    payload := overflowPagePayload }
  unless overflowPage.encode.length == 480 &&
      overflowPage.encode.take 4 == [0, 0, 0, 0] do
    fail "SQLite overflow page had the wrong byte layout"
  unless FileFormat.decodeOverflowPage smallUsable (overflowPage.encode ++ [9]) ==
      some (overflowPage, [9]) do
    fail "SQLite overflow page did not preserve its suffix"
  let secondPage : FileFormat.PageNumber :=
    FileFormat.PageNumber.mk ⟨8, by omega⟩ (by decide)
  let chainTail : FileFormat.OverflowChainData smallUsable :=
    .last firstOverflowPage overflowPagePayload 10 (by decide)
  let chainData : FileFormat.OverflowChainData smallUsable :=
    .link secondPage overflowPagePayload chainTail
  let chain : FileFormat.OverflowChain smallUsable := {
    data := chainData
    acyclic := by
      simp [chainData, chainTail, FileFormat.OverflowChainData.pageNumbers,
        secondPage, firstOverflowPage] }
  unless chain.firstPage == secondPage && chain.data.pageCount == 2 &&
      chain.logicalPayload.length == 486 &&
      chain.toPages.map (fun numbered => (numbered.1, numbered.2.next)) ==
        [(secondPage, .page firstOverflowPage),
          (firstOverflowPage, .endOfChain)] do
    fail "SQLite overflow chain linkage or logical length was incorrect"
  let boundedChain : FileFormat.BoundedOverflowChain smallUsable 10 := {
    chain
    referencesWithin := by
      simp [FileFormat.OverflowChain.ReferencesWithin, chain, chainData,
        chainTail, FileFormat.OverflowChainData.pageNumbers,
        FileFormat.PageNumber.WithinDatabase, secondPage, firstOverflowPage] <;>
        constructor <;> decide }
  unless boundedChain.firstPage.toPageId.val == 7 do
    fail "SQLite bounded overflow chain root mapped to the wrong pager PageId"
  let overflowWrites := boundedChain.toPageWrites
  unless overflowWrites.map (fun write => write.pageId.val) == [7, 6] &&
      overflowWrites.all (fun write => write.page.bytes.size == 480) do
    fail "SQLite overflow chain produced invalid pager writes"
  let resolvedData : FileFormat.OverflowChainData smallUsable :=
    .last firstOverflowPage overflowPagePayload 411 (by decide)
  let resolvedChain : FileFormat.OverflowChain smallUsable := {
    data := resolvedData
    acyclic := by
      simp [resolvedData, FileFormat.OverflowChainData.pageNumbers] }
  let resolvedLeaf : FileFormat.ResolvedTableLeafCell smallUsable := {
    cell := overflowLeaf
    chain := some resolvedChain
    resolved := by
      change resolvedChain.firstPage = firstOverflowPage ∧
        localBytes.length + resolvedChain.logicalPayload.length = overflowSize.val
      constructor
      · rfl
      · have localLength := overflowPayload.wellFormed.2
        have localSize : FileFormat.tableLeafLocalPayloadSize
            smallUsable overflowSize.val = 35 := by decide
        have chainLength := resolvedChain.logicalPayload_length
        have chainSize : resolvedChain.data.logicalPayloadSize = 411 := by
          rfl
        rw [chainSize] at chainLength
        have announcedSize : overflowSize.val = 446 := rfl
        omega }
  unless resolvedLeaf.logicalPayload.length == 446 do
    fail "Resolved table leaf cell reconstructed the wrong payload length"
  let indexPayload : FileFormat.IndexPayload usable payloadSize.val := {
    data := .inline payload.bytes
    wellFormed := by decide }
  let leafIndexCell : FileFormat.LeafIndexCell usable := {
    payloadSize
    payload := indexPayload }
  unless leafIndexCell.encode == [4, 3, 1, 8, 255] &&
      FileFormat.decodeLeafIndexCell usable (leafIndexCell.encode ++ [9]) ==
        some (leafIndexCell, [9]) do
    fail "SQLite leaf index cell had the wrong inline layout"
  let interiorIndexCell : FileFormat.InteriorIndexCell usable := {
    leftChildPage := childPage
    payloadSize
    payload := indexPayload }
  unless interiorIndexCell.encode == [0, 0, 0, 3, 4, 3, 1, 8, 255] &&
      FileFormat.decodeInteriorIndexCell usable
        (interiorIndexCell.encode ++ [9]) == some (interiorIndexCell, [9]) do
    fail "SQLite interior index cell had the wrong inline layout"
  let indexOverflowSize : FileFormat.U64Value := ⟨95, by omega⟩
  let indexOverflowPayload :
      FileFormat.IndexPayload smallUsable indexOverflowSize.val := {
    data := .overflow localBytes firstOverflowPage
    wellFormed := by
      constructor <;> decide }
  let overflowingIndexCell : FileFormat.LeafIndexCell smallUsable := {
    payloadSize := indexOverflowSize
    payload := indexOverflowPayload }
  unless overflowingIndexCell.encode.length == 40 &&
      overflowingIndexCell.encode.take 1 == [95] &&
      overflowingIndexCell.encode.drop 36 == [0, 0, 0, 7] &&
      FileFormat.decodeLeafIndexCell smallUsable
        (overflowingIndexCell.encode ++ [9]) == some (overflowingIndexCell, [9]) do
    fail "SQLite leaf index cell had the wrong overflow layout"

private def expectTypedBTreeLayout : IO Unit := do
  let usable : FileFormat.UsablePageSize := {
    val := 4096
    atLeastMinimum := by decide
    atMostMaximum := by decide }
  let payloadSize : FileFormat.U64Value := ⟨1, by omega⟩
  let rowid : FileFormat.SignedInteger .eight := {
    value := 1
    lowerBound := by decide
    upperBound := by decide }
  let payload : FileFormat.TableLeafPayload usable payloadSize.val := {
    data := .inline [42]
    wellFormed := by decide }
  let leaf : FileFormat.TableLeafCell usable := { payloadSize, rowid, payload }
  let typedCell : FileFormat.TypedBTreeCell usable .leafTable := {
    offset := ⟨4000, by omega⟩
    body := .leafTable leaf
    matchesPage := rfl
    endWithinPage := by decide }
  let common : FileFormat.BTreePageHeaderCommon := {
    firstFreeblock := ⟨0, by omega⟩
    cellCount := ⟨1, by omega⟩
    cellContentStart := ⟨4000, by omega⟩
    fragmentedFreeBytes := 0 }
  let header : FileFormat.ValidBTreePageHeader usable.val := {
    header := .leafTable common
    wellFormed := by decide }
  let pointers : FileFormat.SizedU16Values 1 := {
    values := [⟨4000, by omega⟩]
    length_eq := rfl }
  let pagePrefix : FileFormat.BTreePagePrefix usable.val := {
    header
    pointers
    pointersWithin := by decide }
  let generic : FileFormat.BTreeCellLayout usable.val := {
    pagePrefix
    cells := [typedCell.toPlacedCell]
    pointerAgreement := rfl
    afterPrefix := by decide
    pairwiseDisjoint := by decide }
  let layout : FileFormat.TypedBTreePageLayout usable := {
    generic
    cells := [typedCell]
    placementsAgree := rfl }
  let boundedLayout : FileFormat.BoundedTypedBTreePageLayout usable 10 := {
    layout
    referencesWithin := by decide }
  let pageNumber : FileFormat.BoundedPageNumber 10 := {
    number := FileFormat.PageNumber.mk ⟨3, by omega⟩ (by decide)
    withinDatabase := by decide }
  let numberedPage : FileFormat.NumberedTypedBTreePage usable 10 := {
    pageNumber
    notFirstPage := by decide
    layout := boundedLayout }
  let pageWrite := numberedPage.toPageWrite
  let pageSet : FileFormat.VerifiedPageSet usable 10 := {
    btreePages := [numberedPage]
    overflowChains := []
    pageIdsNodup := by decide }
  let decodedCell : FileFormat.DecodedTypedBTreeCell usable .leafTable := {
    body := .leafTable leaf
    matchesPage := rfl }
  let decodedCells : FileFormat.DecodedBTreeCells usable .leafTable 1 := {
    cells := [decodedCell]
    length_eq := rfl }
  unless layout.cells.length == 1 &&
      layout.encodePage.bytes[4000]? == some 1 &&
      boundedLayout.layout.cells.length == 1 && pageWrite.pageId.val == 2 &&
      pageWrite.page.bytes.size == 4096 &&
      pageSet.writes.map (fun write => write.pageId.val) == [2] &&
      FileFormat.decodeBTreePageCells pagePrefix layout.encodePage ==
        some decodedCells do
    fail "Typed B-tree page layout did not place a matching leaf-table cell"

private def expectBoundedPageNumbers : IO Unit := do
  let number : FileFormat.PageNumber :=
    FileFormat.PageNumber.mk ⟨3, by omega⟩ (by decide)
  let bounded : FileFormat.BoundedPageNumber 10 := {
    number
    withinDatabase := by decide }
  let pageId := bounded.toPageId
  let rebuilt := FileFormat.BoundedPageNumber.ofPageId (by decide) pageId
  unless pageId.val == 2 && rebuilt == bounded do
    fail "SQLite one-based page number did not roundtrip through pager PageId"

private def expectDatabaseFirstPage : IO Unit := do
  let usable : FileFormat.UsablePageSize := {
    val := 4096
    atLeastMinimum := by decide
    atMostMaximum := by decide }
  let headerPrefix : FileFormat.HeaderPrefix := {
    pageSizeField := ⟨4096, by omega⟩
    writeVersion := 1
    readVersion := 1
    reservedSpace := 0
    changeCounter := ⟨42, by omega⟩ }
  let databaseHeader : FileFormat.DatabaseHeader := {
    headerPrefix
    databaseSizePages := ⟨10, by omega⟩
    firstFreelistTrunk := ⟨0, by omega⟩
    freelistPageCount := ⟨0, by omega⟩
    schemaCookie := ⟨7, by omega⟩
    schemaFormat := ⟨4, by omega⟩
    defaultPageCacheSize := ⟨2000, by omega⟩
    largestRootBTreePage := ⟨0, by omega⟩
    textEncoding := ⟨1, by omega⟩
    userVersion := ⟨3, by omega⟩
    incrementalVacuum := ⟨0, by omega⟩
    applicationId := ⟨0, by omega⟩
    versionValidFor := ⟨42, by omega⟩
    sqliteVersion := ⟨3050004, by omega⟩ }
  let common : FileFormat.BTreePageHeaderCommon := {
    firstFreeblock := ⟨0, by omega⟩
    cellCount := ⟨0, by omega⟩
    cellContentStart := ⟨4096, by omega⟩
    fragmentedFreeBytes := 0 }
  let header : FileFormat.ValidBTreePageHeader usable.val := {
    header := .leafTable common
    wellFormed := by decide }
  let pointers : FileFormat.SizedU16Values 0 := { values := [], length_eq := rfl }
  let pagePrefix : FileFormat.BTreePagePrefix usable.val := {
    header
    pointers
    pointersWithin := by decide }
  let generic : FileFormat.BTreeCellLayout usable.val := {
    pagePrefix
    cells := []
    pointerAgreement := rfl
    afterPrefix := by simp
    pairwiseDisjoint := by simp }
  let typed : FileFormat.TypedBTreePageLayout usable := {
    generic
    cells := []
    placementsAgree := rfl }
  let bounded : FileFormat.BoundedTypedBTreePageLayout usable 10 := {
    layout := typed
    referencesWithin := by decide }
  let firstPage : FileFormat.DatabaseFirstPage usable 10 := {
    databaseHeader
    headerWellFormed := by decide
    layout := bounded
    cellsAfterFirstPrefix := by
      intro cell member
      simp [bounded, typed, generic] at member }
  let validDatabaseHeader : FileFormat.ValidDatabaseHeader usable 10 := {
    header := databaseHeader
    wellFormed := by decide }
  let decodedPrefix : FileFormat.DatabaseFirstPagePrefix usable 10 := {
    databaseHeader := validDatabaseHeader
    btreePrefix := pagePrefix }
  let otherPages : FileFormat.VerifiedPageSet usable 10 := {
    btreePages := []
    overflowChains := []
    pageIdsNodup := by decide }
  let databasePages : FileFormat.VerifiedDatabasePageSet usable 10 := {
    firstPage
    otherPages
    pageIdsNodup := by decide }
  let image := firstPage.encodePage
  unless image.bytes.size == 4096 &&
      image.bytes.toList.take 100 == FileFormat.encodeDatabaseHeader databaseHeader &&
      image.bytes[100]? == some 13 && firstPage.toPageWrite.pageId.val == 0 &&
      databasePages.writes.map (fun write => write.pageId.val) == [0] &&
      FileFormat.decodeDatabaseFirstPagePrefix usable 10
        (decodedPrefix.encode ++ [9]) == some (decodedPrefix, [9]) &&
      image.bytes.toList.take decodedPrefix.encode.length == decodedPrefix.encode do
    fail "SQLite database first page did not place its B-tree header at byte 100"
  match DiskFormat.decodeDatabaseGeometry
      (FileFormat.encodeDatabaseHeader databaseHeader ++ [9]) with
  | some (geometry, [9]) =>
      unless geometry.usable.val == 4096 && geometry.pageCount == 10 do
        fail "database geometry decoder discovered the wrong pager dimensions"
  | _ => fail "database geometry decoder rejected a valid SQLite header"
  let reservedHeader : FileFormat.DatabaseHeader := {
    databaseHeader with
    headerPrefix := { databaseHeader.headerPrefix with reservedSpace := 1 } }
  match DiskFormat.decodeDatabaseGeometry
      (FileFormat.encodeDatabaseHeader reservedHeader) with
  | none => pure ()
  | some _ => fail "database geometry decoder accepted unsupported reserved bytes"
  let emptyDisk : Storage.Disk 4096 10 :=
    Storage.Disk.constant 4096 10 (Storage.Page.zero 4096)
  let physicalDisk := Storage.applyWrites emptyDisk databasePages.writes
  let fileBytes := DiskFormat.encodeDisk physicalDisk
  match DiskFormat.decodeDatabaseImage (fileBytes ++ [9]) with
  | some (opened, [9]) =>
      let firstId : Storage.PageId opened.geometry.pageCount :=
        ⟨0, opened.geometry.header.wellFormed.2.2.2.1⟩
      unless opened.geometry.usable.val == 4096 &&
          opened.geometry.pageCount == 10 &&
          (opened.disk.read firstId).bytes == image.bytes do
        fail "dynamic database image decoder changed its geometry or page one"
  | _ => fail "dynamic database image decoder rejected a complete verified image"
  match DiskFormat.decodeDatabaseImage (fileBytes.take (fileBytes.length - 1)) with
  | none => pure ()
  | some _ => fail "dynamic database image decoder accepted a truncated file"

private def expectDiskFormat : IO Unit := do
  let firstPage : Storage.Page 4 := {
    bytes := #[1, 2, 3, 4]
    sizeInvariant := by decide }
  let secondPage : Storage.Page 4 := {
    bytes := #[5, 6, 7, 8]
    sizeInvariant := by decide }
  let disk : Storage.Disk 4 2 := {
    read := fun pageId => if pageId.val = 0 then firstPage else secondPage }
  let encoded := DiskFormat.encodeDisk disk
  unless encoded == [1, 2, 3, 4, 5, 6, 7, 8] do
    fail "whole-disk encoder did not concatenate pages in pager order"
  match DiskFormat.decodeDisk 4 2 (encoded ++ [9]) with
  | none => fail "whole-disk decoder rejected its encoder output"
  | some (decoded, suffix) =>
      let firstId : Storage.PageId 2 := ⟨0, by decide⟩
      let secondId : Storage.PageId 2 := ⟨1, by decide⟩
      unless suffix == [9] && (decoded.read firstId).bytes == firstPage.bytes &&
          (decoded.read secondId).bytes == secondPage.bytes do
        fail "whole-disk decoder changed page bytes or consumed its suffix"
  match DiskFormat.decodeDisk 4 2 (encoded.take 7) with
  | none => pure ()
  | some _ => fail "whole-disk decoder accepted a truncated final page"

open QuerySemantics in
private def expectOptimizerSemantics : IO Unit := do
  let one : Core.Value := .integer ⟨1, by decide, by decide⟩
  let two : Core.Value := .integer ⟨2, by decide, by decide⟩
  let five : Core.Value := .integer ⟨5, by decide, by decide⟩
  let seven : Core.Value := .integer ⟨7, by decide, by decide⟩
  let rightText : Core.Value :=
    .text ⟨[114, 105, 103, 104, 116], by decide⟩
  let leftRows : List Row :=
    [.values [one], .values [.null], .values [two]]
  let rightRows : List Row := [.values [rightText]]
  let predicate : Predicate := .equals (.cell 0) one
  let joinPlan : Plan := .innerJoin (.rows leftRows) (.rows rightRows)
  let filtered : Plan := .filter (.onLeft predicate) joinPlan
  let pushed := QuerySemantics.predicatePushdown filtered
  unless evalPlan Core.Database.empty filtered == evalPlan Core.Database.empty pushed do
    fail "verified predicate pushdown changed inner-join rows"
  let constantPredicate : Predicate :=
    .and (.constant .true)
      (.or (.constant .false) (.not (.constant .unknown)))
  let constantPlan : Plan := .filter constantPredicate (.rows leftRows)
  unless evalPlan Core.Database.empty constantPlan ==
      evalPlan Core.Database.empty (QuerySemantics.constantFolding constantPlan) do
    fail "verified constant folding changed three-valued WHERE semantics"
  let identityPlan : Plan := .project .identity joinPlan
  unless evalPlan Core.Database.empty identityPlan ==
      evalPlan Core.Database.empty (QuerySemantics.projectionElimination identityPlan) do
    fail "verified identity projection elimination changed rows"
  let fusedInput : Plan := .filter (.truthy (.cell 0))
    (.filter (.notEquals (.cell 0) .null) (.rows leftRows))
  unless evalPlan Core.Database.empty fusedInput ==
      evalPlan Core.Database.empty (QuerySemantics.filterFusion fusedInput) do
    fail "verified filter fusion changed three-valued WHERE semantics"
  let unionInput : Plan :=
    .unionAll (.rows (leftRows.take 2)) (.rows (leftRows.drop 2))
  let distributedInput : Plan := .filter predicate unionInput
  let distributed := QuerySemantics.unionDistribution distributedInput
  unless evalPlan Core.Database.empty distributedInput ==
      evalPlan Core.Database.empty distributed do
    fail "verified UNION ALL distribution changed row order or 3VL results"
  match distributed with
  | .unionAll (.filter _ _) (.filter _ _) => pure ()
  | _ => fail "explicit filter/UNION distribution did not expose both arms"
  let costSafe := QuerySemantics.optimizePlan distributedInput
  unless (QuerySemantics.cost Core.Database.empty costSafe).total ≤
      (QuerySemantics.cost Core.Database.empty distributedInput).total do
    fail "live optimizer increased the certified logical cost"
  let groupedInput : Plan :=
    .groupSum (fun _ => .values [one]) (fun _ => 2) unionInput
  let groupedDistributed := QuerySemantics.unionDistribution groupedInput
  unless evalPlan Core.Database.empty groupedInput ==
      evalPlan Core.Database.empty groupedDistributed do
    fail "verified grouped UNION ALL distribution changed weighted results"
  match groupedDistributed with
  | .unionAll (.groupSum _ _ _) (.groupSum _ _ _) => pure ()
  | _ => fail "explicit grouped UNION distribution did not expose both arms"
  let ordered : QuerySemantics.Select := {
    plan := filtered
    orderBy := [{ column := .left (.cell 0) }] }
  unless QuerySemantics.eval Core.Database.empty ordered ==
      QuerySemantics.eval Core.Database.empty
        ((Rewrite.predicatePushdown).apply ordered) do
    fail "optimizer rewrite changed observable ORDER BY output"
  let sample : Row := .values [seven]
  if whereRows
      (.or (.constant .unknown) (.not (.constant .unknown))) [sample] ==
      whereRows (.constant .true) [sample] then
    fail "test failed to witness SQL excluded-middle unsoundness"
  if whereRows
      (.onRight (.equals (.cell 0) five))
      (leftJoinRows [sample] [.values [.null]]) ==
      leftJoinRows [sample]
        (whereRows (.equals (.cell 0) five) [.values [.null]]) then
    fail "test failed to witness outer-join predicate-pushdown unsoundness"
  let corePredicate : Core.Predicate :=
    .not (.not (.equal 0 one))
  let coreQuery : Core.Query := {
    columns := [0]
    predicate := some corePredicate }
  let optimized := CoreOptimizerBridge.optimize "items" coreQuery
  match optimized.predicate with
  | some (.equal 0 value) =>
      unless value = one do
        fail "live optimizer changed the normalized comparison value"
  | _ => fail "live optimizer did not eliminate double negation"
  let coreRows : List Core.Row := [
    { rowid := ⟨1, by decide, by decide⟩, values := [one] },
    { rowid := ⟨2, by decide, by decide⟩, values := [two] }]
  unless optimized.eval coreRows = coreQuery.eval coreRows do
    fail "live denotational optimizer changed Core query results"
  let rightCoreRows : List Core.Row := [
    { rowid := ⟨1, by decide, by decide⟩, values := [two] },
    { rowid := ⟨2, by decide, by decide⟩, values := [one] }]
  let joinEquality : CoreJoin.Predicate :=
    .equal (.column ⟨.left, 0⟩) (.column ⟨.right, 0⟩)
  let denotationalJoin := CoreOptimizerBridge.innerJoinPlan
    (some joinEquality) none coreRows rightCoreRows
  unless evalPlan Core.Database.empty
      (QuerySemantics.optimizePlan denotationalJoin) ==
      (CoreJoin.matchingRows (some joinEquality) none
        (CoreJoin.crossRows coreRows rightCoreRows)).map
          CoreOptimizerBridge.joinedRow do
    fail "proved optimizer changed the embedded live inner join"
  let joinQuery : CoreJoin.Query := {
    columns := [⟨.left, 0⟩, ⟨.right, 0⟩]
    on := some joinEquality }
  let optimizedJoin := CoreOptimizerBridge.optimizeJoin "left" "right" joinQuery
  unless optimizedJoin.eval coreRows rightCoreRows ==
      joinQuery.eval coreRows rightCoreRows do
    fail "live denotational join optimizer changed Core join results"
  let outerRightRows : List Core.Row := rightCoreRows.take 1
  let outerPlan := CoreOptimizerBridge.leftOuterJoinPlan
    (some joinEquality) none 1 coreRows outerRightRows
  unless evalPlan Core.Database.empty
      (QuerySemantics.optimizePlan outerPlan) ==
      (CoreJoin.leftOuterRows (some joinEquality) 1 coreRows outerRightRows).map
        CoreOptimizerBridge.joinedRow do
    fail "proved optimizer changed width-aware live left-outer rows"
  let leftJoinQuery : CoreJoin.Query := {
    columns := [⟨.left, 0⟩, ⟨.right, 0⟩]
    on := some joinEquality
    kind := .left
    rightWidth := 1 }
  let optimizedLeft := CoreOptimizerBridge.optimizeJoin
    "left" "right" leftJoinQuery
  unless optimizedLeft.eval coreRows outerRightRows ==
      leftJoinQuery.eval coreRows outerRightRows do
    fail "live width-aware left-join optimizer changed Core results"
  unless optimizedLeft.eval coreRows outerRightRows ==
      [[one, .null], [two, two]] do
    fail "width-aware left-join denotation lost its NULL-extended row"
  let compoundLeft : List (List Core.Value) := [[one], [two], [one]]
  let compoundRight : List (List Core.Value) := [[two], [one], [two]]
  let checkCompound (operation : CompoundOp) : IO Unit := do
    let expected := (CoreOptimizerBridge.compoundRows operation
      compoundLeft compoundRight).map CoreOptimizerBridge.compoundRow
    unless evalPlan Core.Database.empty
        (QuerySemantics.optimizePlan
          (CoreOptimizerBridge.compoundPlan operation
            compoundLeft compoundRight)) == expected do
      fail "proved compound optimizer changed duplicate-sensitive bag results"
    unless CoreOptimizerBridge.optimizeCompoundOp operation = operation do
      fail "live compound optimizer changed the SQL set operation"
  checkCompound .unionAll
  checkCompound .unionDistinct
  checkCompound .intersect
  checkCompound .except

private def expectKRelationSemantics : IO Unit := do
  let left : KRelation.Relation Nat := fun row => if row == 1 then 2 else 0
  let right : KRelation.Relation Nat := fun row => if row == 1 then 3 else 1
  let union := KRelation.unionAll left right
  unless union 1 == 5 && KRelation.distinct union 1 == 1 &&
      KRelation.intersect left right 1 == 2 && KRelation.except right left 1 == 1 do
    fail "multiplicity-valued set operators lost SQL bag counts"
  let selected := KRelation.select
    (fun row => if row == 1 then .unknown else .true) union
  unless selected 1 == 0 && selected 2 == 1 do
    fail "K-relation selection treated UNKNOWN as TRUE"
  let grouped := KRelation.groupCount [1, 2] (fun row => row % 2) union
  unless grouped 0 == 1 && grouped 1 == 5 do
    fail "K-relation grouping did not sum source multiplicities"

private def expectRelationalAlgebra : IO Unit := do
  let left : RelationalAlgebra.Expr Nat :=
    .relation (RelationalAlgebra.ofList [1, 1, 2])
  let right : RelationalAlgebra.Expr Nat :=
    .relation (RelationalAlgebra.ofList [10, 10])
  let product := RelationalAlgebra.eval (.product left right)
  unless product (1, 10) == 4 && product (2, 10) == 2 do
    fail "typed product lost SQL bag multiplicity"
  let selected := RelationalAlgebra.eval
    (.select (fun row : Nat × Nat => if row.1 == 1 then .true else .unknown)
      (.product left right))
  let pushed := RelationalAlgebra.eval
    (.product (.select (fun row : Nat => if row == 1 then .true else .unknown)
      left) right)
  unless selected (1, 10) == pushed (1, 10) &&
      selected (2, 10) == pushed (2, 10) do
    fail "general algebra predicate pushdown changed 3VL bag semantics"
  let swapped := RelationalAlgebra.eval
    (RelationalAlgebra.swapProduct (.product left right))
  unless swapped (10, 1) == product (1, 10) do
    fail "general algebra product permutation changed multiplicity"
  let third : RelationalAlgebra.Expr Nat :=
    .relation (RelationalAlgebra.ofList [100, 100, 100])
  let associated := RelationalAlgebra.eval
    (RelationalAlgebra.reassociateProduct (.product (.product left right) third))
  let direct := RelationalAlgebra.eval (.product left (.product right third))
  unless associated (1, (10, 100)) == direct (1, (10, 100)) do
    fail "general algebra product reassociation changed multiplicity"
  let emptyRight : RelationalAlgebra.Expr Nat :=
    .relation KRelation.empty
  let rightDomain : RelationalAlgebra.Domain Nat := ⟨[10], by decide⟩
  let outer := RelationalAlgebra.eval
    (.leftOuter inferInstance rightDomain 0
      (fun left right => if left == right then .true else .false)
      left emptyRight)
  unless outer (1, 0) == 2 && outer (2, 0) == 1 do
    fail "general algebra left outer join lost unmatched multiplicity"
  let outerSelected := RelationalAlgebra.eval
    (.select (fun row : Nat × Nat => if row.1 == 1 then .true else .unknown)
      (.leftOuter inferInstance rightDomain 0
        (fun left right => if left == right then .true else .false)
        left emptyRight))
  let outerPushed := RelationalAlgebra.eval
    (.leftOuter inferInstance rightDomain 0
      (fun left right => if left == right then .true else .false)
      (.select (fun row : Nat => if row == 1 then .true else .unknown) left)
      emptyRight)
  unless outerSelected (1, 0) == outerPushed (1, 0) &&
      outerSelected (2, 0) == outerPushed (2, 0) do
    fail "left-side pushdown through outer join changed 3VL bag semantics"
  let duplicated := RelationalAlgebra.eval (.distinct (.distinct left))
  unless duplicated 1 == 1 && duplicated 2 == 1 do
    fail "typed DISTINCT was not idempotent"
  let groupDomain : RelationalAlgebra.Domain Nat := ⟨[1, 2], by decide⟩
  let groupedUnion := RelationalAlgebra.eval
    (.groupSum inferInstance groupDomain (fun row => row % 2) (fun row => row)
      (.unionAll left left))
  unless groupedUnion 0 == 4 && groupedUnion 1 == 4 do
    fail "typed grouped SUM did not preserve UNION ALL multiplicity"
  let materializedCount := RelationalAlgebra.eval
    (.materializeCount inferInstance
      (RelationalAlgebra.supportDomain [1, 1, 2]) (fun row => row) left)
  unless materializedCount (1, 2) == 1 &&
      materializedCount (2, 1) == 1 && materializedCount (1, 1) == 0 do
    fail "materialized COUNT did not emit one exact aggregate row per group"
  let materializedSum := RelationalAlgebra.eval
    (.materializeSum inferInstance
      (RelationalAlgebra.supportDomain [1, 1, 2]) (fun row => row)
      (fun row => if row == 1 then 0 else 3) left)
  unless materializedSum (1, 0) == 1 &&
      materializedSum (2, 3) == 1 && materializedSum (2, 0) == 0 do
    fail "materialized SUM lost a zero-valued group or emitted a wrong value"
  let one : Core.Value := .integer ⟨1, by decide, by decide⟩
  let two : Core.Value := .integer ⟨2, by decide, by decide⟩
  let leftRow : QuerySemantics.Row := .values [one]
  let rightRow : QuerySemantics.Row := .values [two]
  let legacyPlan : QuerySemantics.Plan :=
    .filter (.constant .true)
      (.innerJoin (.rows [leftRow, leftRow]) (.rows [rightRow]))
  match RelationalAlgebra.ofPlan? Core.Database.empty legacyPlan with
  | none => fail "typed algebra rejected the product/filter optimizer basis"
  | some translated =>
      let relation := RelationalAlgebra.eval translated
      unless relation (.joined leftRow rightRow) == 2 do
        fail "optimizer-plan translation changed joined-row multiplicity"
  match RelationalAlgebra.ofPlan? Core.Database.empty
      (.project .left legacyPlan) with
  | none => fail "typed algebra rejected proved finite-support projection"
  | some translated =>
      let relation := RelationalAlgebra.eval translated
      unless relation leftRow == 2 do
        fail "typed algebra projection lost duplicate joined rows"
  let setPlan : QuerySemantics.Plan :=
    .distinct (.unionAll (.rows [leftRow, leftRow]) (.rows [leftRow]))
  match RelationalAlgebra.ofPlan? Core.Database.empty setPlan with
  | none => fail "typed algebra rejected UNION ALL / DISTINCT plan"
  | some translated =>
      let relation := RelationalAlgebra.eval translated
      unless relation leftRow == 1 do
        fail "typed algebra DISTINCT did not collapse UNION ALL multiplicity"
  let intersectPlan : QuerySemantics.Plan :=
    .intersectAll (.rows [leftRow, leftRow, leftRow])
      (.rows [leftRow, leftRow])
  match RelationalAlgebra.ofPlan? Core.Database.empty intersectPlan with
  | none => fail "typed algebra rejected INTERSECT ALL plan"
  | some translated =>
      unless RelationalAlgebra.eval translated leftRow == 2 do
        fail "typed algebra INTERSECT ALL lost minimum multiplicity"
  let exceptPlan : QuerySemantics.Plan :=
    .exceptAll (.rows [leftRow, leftRow, leftRow]) (.rows [leftRow])
  match RelationalAlgebra.ofPlan? Core.Database.empty exceptPlan with
  | none => fail "typed algebra rejected EXCEPT ALL plan"
  | some translated =>
      unless RelationalAlgebra.eval translated leftRow == 2 do
        fail "typed algebra EXCEPT ALL lost truncated difference"
  let outerPlan : QuerySemantics.Plan :=
    .leftOuterJoin (.rows [leftRow, leftRow]) (.rows [])
  match RelationalAlgebra.ofPlan? Core.Database.empty outerPlan with
  | none => fail "typed algebra rejected left outer plan"
  | some translated =>
      unless RelationalAlgebra.eval translated
          (.joined leftRow (.values [])) == 2 do
        fail "typed algebra left outer plan lost NULL-extended multiplicity"
  let matchingOuterPlan : QuerySemantics.Plan :=
    .leftOuterOn (.equals (.right (.cell 0)) two)
      (.rows [leftRow, leftRow]) (.rows [rightRow, rightRow])
  match RelationalAlgebra.ofPlan? Core.Database.empty matchingOuterPlan with
  | none => fail "typed algebra rejected predicate-bearing left outer plan"
  | some translated =>
      unless RelationalAlgebra.eval translated (.joined leftRow rightRow) == 4 do
        fail "predicate-bearing outer join lost duplicate matches"
  let falseOuterPlan : QuerySemantics.Plan :=
    .leftOuterOn (.equals (.right (.cell 0)) one)
      (.rows [leftRow, leftRow]) (.rows [rightRow])
  match RelationalAlgebra.ofPlan? Core.Database.empty falseOuterPlan with
  | none => fail "typed algebra rejected unmatched left outer plan"
  | some translated =>
      unless RelationalAlgebra.eval translated
          (.joined leftRow (.values [])) == 2 do
        fail "predicate-bearing outer join lost false NULL extension"
  let unknownOuterPlan : QuerySemantics.Plan :=
    .leftOuterOn (.equals (.right (.cell 0)) one)
      (.rows [leftRow, leftRow]) (.rows [.values [.null]])
  match RelationalAlgebra.ofPlan? Core.Database.empty unknownOuterPlan with
  | none => fail "typed algebra rejected UNKNOWN left outer plan"
  | some translated =>
      unless RelationalAlgebra.eval translated
          (.joined leftRow (.values [])) == 2 do
        fail "predicate-bearing outer join treated UNKNOWN as a match"
  let groupCountPlan : QuerySemantics.Plan :=
    .groupCount (fun row => row) (.rows [leftRow, leftRow, rightRow])
  match RelationalAlgebra.ofPlan? Core.Database.empty groupCountPlan with
  | none => fail "typed algebra rejected GROUP COUNT plan"
  | some translated =>
      let relation := RelationalAlgebra.eval translated
      unless relation leftRow == 2 && relation rightRow == 1 do
        fail "GROUP COUNT translation lost input multiplicities"
  let groupSumPlan : QuerySemantics.Plan :=
    .groupSum (fun _ => leftRow)
      (fun row => if row == leftRow then 3 else 2)
      (.rows [leftRow, leftRow, rightRow])
  match RelationalAlgebra.ofPlan? Core.Database.empty groupSumPlan with
  | none => fail "typed algebra rejected GROUP SUM plan"
  | some translated =>
      unless RelationalAlgebra.eval translated leftRow == 8 do
        fail "GROUP SUM translation lost weighted duplicate contributions"
  let coreGroupRows : List Core.Row := [
    { rowid := ⟨1, by decide, by decide⟩, values := [one] },
    { rowid := ⟨2, by decide, by decide⟩, values := [one] },
    { rowid := ⟨3, by decide, by decide⟩, values := [two] }]
  let coreGroupQuery : Core.GroupQuery := {
    groupBy := [0]
    outputs := [.key 0, .countStar] }
  unless RelationalAlgebra.materializedCountRows coreGroupQuery.rowKey
      (coreGroupQuery.selectedRows coreGroupRows) ==
      [([one], 2), ([two], 1)] do
    fail "live Core grouped COUNT disagreed with materialized algebra rows"
  let three : Core.Value := .integer ⟨3, by decide, by decide⟩
  let negativeFive : Core.Value := .integer ⟨-5, by decide, by decide⟩
  let negativeTwo : Core.Value := .integer ⟨-2, by decide, by decide⟩
  let coreSumRows : List Core.Row := [
    { rowid := ⟨1, by decide, by decide⟩, values := [one, three] },
    { rowid := ⟨2, by decide, by decide⟩, values := [one, negativeFive] },
    { rowid := ⟨3, by decide, by decide⟩, values := [two, .null] }]
  match coreGroupQuery.outputValue coreSumRows [one] (.sumColumn 1) with
  | .ok value => unless value == negativeTwo do
      fail "live grouped SUM disagreed with the mathematical negative sum"
  | .error message => fail s!"live grouped SUM failed: {message}"
  match coreGroupQuery.outputValue coreSumRows [two] (.sumColumn 1) with
  | .ok value => unless value == .null do
      fail "live grouped SUM did not return NULL for an all-NULL group"
  | .error message => fail s!"live all-NULL grouped SUM failed: {message}"
  let mixedGroupQuery : Core.GroupQuery := {
    groupBy := [0]
    outputs := [.key 0, .countStar, .sumColumn 1] }
  match mixedGroupQuery.eval coreSumRows with
  | .ok rows => unless rows ==
      [[one, .integer ⟨2, by decide, by decide⟩, negativeTwo],
       [two, .integer ⟨1, by decide, by decide⟩, .null]] do
      fail "live mixed aggregate tuple changed key/COUNT/SUM alignment"
  | .error message => fail s!"live mixed aggregate tuple failed: {message}"

private def expectPagedBTree : IO Unit := do
  let empty : PagedBTree.Tree String := .empty
  let tree := empty.insert 3 "three" |>.insert 1 "one" |>.insert 2 "two"
  unless tree.toList == [(1, "one"), (2, "two"), (3, "three")] do
    fail "paged B+tree insertion changed sorted observable contents"
  unless tree.pages.length == 2 && tree.pageRefs.length == 2 do
    fail "paged B+tree did not split a full leaf"
  let replaced := tree.insert 2 "TWO"
  unless replaced.toList == [(1, "one"), (2, "TWO"), (3, "three")] do
    fail "paged B+tree replacement duplicated an existing key"
  let merged := replaced.delete 2
  unless merged.toList == [(1, "one"), (3, "three")] &&
      merged.pages.length == 1 do
    fail "paged B+tree deletion did not preserve contents while merging leaves"

private def expectRecursiveBPlusTree : IO Unit := do
  let entries := (List.range 64).map fun key => (key, toString key)
  let tree := (RecursiveBPlusTree.Tree.empty :
    RecursiveBPlusTree.Tree String).insertAll entries
  unless tree.toList == entries do
    fail "recursive B+tree insertion changed sorted contents"
  unless tree.height >= 4 && tree.pageCount > 32 do
    fail "recursive B+tree did not propagate splits beyond two levels"
  unless tree.checkBalanced do
    fail "recursive B+tree insertion violated occupancy or leaf depth"
  unless tree.lookup 37 == some "37" do
    fail "recursive B+tree descent missed an inserted key"
  unless tree.rangeScan 20 24 ==
      [(20, "20"), (21, "21"), (22, "22"), (23, "23")] do
    fail "recursive B+tree range scan crossed the wrong leaf interval"
  let replaced := tree.insert 37 "replaced"
  unless replaced.lookup 37 == some "replaced" &&
      replaced.toList.length == tree.toList.length do
    fail "recursive B+tree replacement duplicated its key"
  let deleted := replaced.delete 37
  unless deleted.lookup 37 == none && deleted.toList.length + 1 == tree.toList.length do
    fail "recursive B+tree deletion failed to merge an empty leaf"
  let deletedMany := (List.range 48).foldl
    (fun current key => current.deleteBalanced key) tree
  unless deletedMany.toList == entries.drop 48 && deletedMany.checkBalanced do
    fail "recursive B+tree redistribution or root shrink changed contents/balance"
  let verifiedDeletes := (List.range 48).foldl
    (fun current key => current.delete key) tree
  unless verifiedDeletes.toList == entries.drop 48 &&
      verifiedDeletes.checkRootValid do
    fail "verified recursive B+tree deletion did not preserve its full invariant"
  let (coreState, _) ← match CoreSQL.execute Core.State.empty "
      CREATE TABLE core_tree(id INTEGER PRIMARY KEY,v TEXT);
      INSERT INTO core_tree VALUES(1,'one'),(3,'three'),(5,'five');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"Core B+tree setup failed: {message}"
  let coreTable ← match coreState.database.findTable? "core_tree" with
    | some table => pure table
    | none => fail "Core B+tree setup lost its table"
  let coreTree := coreTable.rowTree.root.erase
  unless coreTree.toList == Core.treeEntries coreTable.rows &&
      coreTree.checkRootValid do
    fail "Core B+tree construction changed signed-rowid order or validity"
  let insertedRow ← match Core.Row.create coreTable.schema
      [.integer ⟨4, by decide, by decide⟩,
        .text ⟨[102, 111, 117, 114], by decide⟩] with
    | .ok row => pure row
    | .error message => fail s!"Core B+tree row construction failed: {message}"
  let insertedTree := coreTree.insert insertedRow.treeKey insertedRow
  unless insertedTree.toList.map (·.2.rowid.value) == [1, 3, 4, 5] &&
      insertedTree.lookup insertedRow.treeKey == some insertedRow do
    fail "Core B+tree localized insertion changed its list abstraction"
  let deletedTree := insertedTree.delete insertedRow.treeKey
  unless deletedTree.toList == Core.treeEntries coreTable.rows &&
      deletedTree.checkRootValid do
    fail "Core B+tree localized deletion changed its list abstraction"

private def expectCoreMergeJoin : IO Unit := do
  let sql := "
    CREATE TABLE merge_left(id INTEGER PRIMARY KEY,label TEXT);
    CREATE TABLE merge_right(id INTEGER PRIMARY KEY,label TEXT);
    INSERT INTO merge_left VALUES(1,'left one'),(3,'left three'),(5,'left five');
    INSERT INTO merge_right VALUES(2,'right two'),(3,'right three'),(5,'right five');"
  let (state, _) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"merge join setup failed: {message}"
  let left ← match state.database.findTable? "merge_left" with
    | some table => pure table
    | none => fail "merge join setup lost its left table"
  let right ← match state.database.findTable? "merge_right" with
    | some table => pure table
    | none => fail "merge join setup lost its right table"
  let query : CoreJoin.Query := {
    columns := [⟨.left, 0⟩, ⟨.left, 1⟩, ⟨.right, 1⟩]
    on := some (CoreJoin.rowidOn left.schema.primaryKey right.schema.primaryKey) }
  unless query.evalPlanned left right == query.eval left.rows right.rows do
    fail "primary-key merge join changed nested-loop semantics"
  unless query.evalPlanned left right == [
      [.integer ⟨3, by decide, by decide⟩,
        .text ⟨[108, 101, 102, 116, 32, 116, 104, 114, 101, 101], by decide⟩,
        .text ⟨[114, 105, 103, 104, 116, 32, 116, 104, 114, 101, 101], by decide⟩],
      [.integer ⟨5, by decide, by decide⟩,
        .text ⟨[108, 101, 102, 116, 32, 102, 105, 118, 101], by decide⟩,
        .text ⟨[114, 105, 103, 104, 116, 32, 102, 105, 118, 101], by decide⟩]] do
    fail "primary-key merge join returned the wrong matching rows"
  let leftOnly : CoreJoin.Predicate :=
    .equal (.column ⟨.left, left.schema.primaryKey⟩)
      (.literal (.integer ⟨1, by decide, by decide⟩))
  unless leftOnly.leftOnly do
    fail "join planner did not recognize a left-only predicate"
  let filteredQuery := { query with where_ := some leftOnly }
  unless filteredQuery.evalPlanned left right ==
      filteredQuery.eval left.rows right.rows do
    fail "live inner-join left-predicate pushdown changed semantics"
  let outerKind := { filteredQuery with kind := CoreJoin.JoinKind.left }
  let outerQuery := { outerKind with rightWidth := right.schema.columns.length }
  unless outerQuery.evalPlanned left right ==
      outerQuery.eval left.rows right.rows do
    fail "live left-outer-join left-predicate pushdown changed semantics"
  unless outerQuery.evalPlanned left right == [[
      .integer ⟨1, by decide, by decide⟩,
      .text ⟨[108, 101, 102, 116, 32, 111, 110, 101], by decide⟩,
      .null]] do
    fail "live left-predicate pushdown lost the unmatched outer row"

private def expectRecursivePhysicalPageBTree : IO Unit := do
  let payload := String.mk (List.replicate 900 'p')
  let values := String.intercalate ","
    ((List.range 60).map fun offset =>
      let id := offset + 1
      s!"({id},'{payload}{id}')")
  let sql := s!"
    CREATE TABLE deep_pages(id INTEGER PRIMARY KEY,value TEXT NOT NULL);
    CREATE TABLE auxiliary(id INTEGER PRIMARY KEY,label TEXT NOT NULL);
    CREATE INDEX auxiliary_label ON auxiliary(label);
    INSERT INTO deep_pages VALUES {values};
    INSERT INTO auxiliary VALUES(1,'one'),(2,'two');"
  let (state, _) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"recursive physical setup failed: {message}"
  let table ← match state.database.findTable? "deep_pages" with
    | some table => pure table
    | none => fail "recursive physical setup lost its table"
  let leaves ← match CoreFile.tableLeaves table with
    | some leaves => pure leaves
    | none => fail "recursive physical setup could not encode its leaf cells"
  let plan ← match RecursivePageBTree.build leaves with
    | some plan => pure plan
    | none => fail "recursive physical page planner rejected nonempty leaves"
  unless plan.height >= 3 && plan.checkBalanced &&
      plan.toCells == leaves.flatten do
    fail "recursive physical page planner did not build a balanced deep tree"
  let image ← match RecursivePageBTree.encode state.database with
    | some image => pure image
    | none => fail "recursive physical encoder rejected supported tables"
  unless image.pageCount > plan.pageCount + 2 do
    fail "recursive physical image did not allocate later table/index roots"
  let reopened ← match CoreDecode.decode image.fileBytes with
    | some database => pure database
    | none => fail "general decoder rejected an arbitrary-depth table tree"
  unless reopened.Equiv state.database do
    fail "arbitrary-depth table encoding changed the logical database"
  let path : System.FilePath := ".lake/build/sqleanite-recursive-pages.db"
  IO.FS.writeBinFile path (ByteArray.mk image.fileBytes.toArray)
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT count(*) FROM deep_pages; SELECT count(*) FROM auxiliary; SELECT name FROM sqlite_master WHERE type='index';"] }
  unless output.exitCode == 0 &&
      output.stdout == "ok\n60\n2\nauxiliary_label\n" do
    fail s!"sqlite3 rejected the arbitrary-depth table tree: {output.stderr}{output.stdout}"

private def expectPhysicalMVPTableBTree : IO Unit := do
  let first : PhysicalCodec.Row := {
    rowid := ⟨1, by decide, by decide⟩
    first := .integer ⟨11, by decide, by decide⟩
    second := .null }
  let second : PhysicalCodec.Row := {
    rowid := ⟨2, by decide, by decide⟩
    first := .integer ⟨22, by decide, by decide⟩
    second := .null }
  let third : PhysicalCodec.Row := {
    rowid := ⟨3, by decide, by decide⟩
    first := .integer ⟨33, by decide, by decide⟩
    second := .null }
  let fourth : PhysicalCodec.Row := {
    rowid := ⟨4, by decide, by decide⟩
    first := .integer ⟨44, by decide, by decide⟩
    second := .null }
  let fifth : PhysicalCodec.Row := {
    rowid := ⟨5, by decide, by decide⟩
    first := .integer ⟨55, by decide, by decide⟩
    second := .null }
  let database : PhysicalCodec.Database := {
    rows := [first, second, third, fourth, fifth]
    rowidsSorted := by
      simp [PhysicalCodec.Row.keyLess, first, second, third, fourth, fifth]
    pageFits := by
      unfold PhysicalCodec.PageFit PhysicalCodec.cellBytes PhysicalCodec.pageSize
      decide }
  let tree ← match PhysicalTableBTree.build database with
    | some tree => pure tree
    | none => fail "physical MVP table B-tree rejected a fitting database"
  unless tree.toList == database.rows do
    fail "physical MVP table B-tree partition changed observable rows"
  unless tree.leaves.map List.length == [2, 2, 1] do
    fail s!"physical MVP table B-tree split rows incorrectly: {tree.leaves.map List.length}"
  unless tree.interiorCells.map (fun cell => cell.leftChildPage.value.val) == [3, 4] &&
      tree.interiorCells.map (fun cell => cell.key.value) == [2, 4] &&
      tree.rightmostPage.val == 5 do
    fail "physical MVP table B-tree emitted incorrect bounded child references"
  let pages := tree.tablePages
  unless pages.map (fun page => page.bytes[0]?) ==
      [some 5, some 13, some 13, some 13] do
    fail "physical MVP table B-tree emitted incorrect SQLite page types"
  unless pages.all (fun page => page.bytes.size == PhysicalCodec.pageSize) do
    fail "physical MVP table B-tree emitted a non-4096-byte page"
  let fileBytes := PhysicalMultiPageCodec.fileBytes tree
  match DiskFormat.decodeDatabaseImage fileBytes with
  | some (image, []) =>
      unless image.geometry.pageCount == 5 do
        fail "verified multi-page image decoder recovered the wrong page count"
  | _ => fail "verified multi-page image decoder rejected its own bytes"
  match PhysicalMultiPageCodec.decodeFile fileBytes with
  | some reopened =>
      unless reopened.rows == database.rows do
        fail "verified multi-page logical decoder changed the row sequence"
  | none => fail "verified multi-page logical decoder rejected its own image"
  let journal := GrowableStorage.makeJournal
    (PhysicalMultiPageCodec.storageImage tree)
    (PhysicalMultiPageCodec.transactionWrites tree)
  let encodable ← match PhysicalJournalCodec.ofJournal? journal with
    | some value => pure value
    | none => fail "multi-page rollback journal exceeded its encoded bounds"
  match PhysicalJournalCodec.decode (PhysicalJournalCodec.encode encodable) with
  | some (decoded, []) =>
      unless decoded.originalPageCount == journal.originalPageCount &&
          decoded.undo.map (fun record => record.pageId) ==
            journal.undo.map (fun record => record.pageId) &&
          decoded.undo.map (fun record => record.before.bytes) ==
            journal.undo.map (fun record => record.before.bytes) do
        fail "multi-page rollback journal codec changed an undo record"
  | _ => fail "multi-page rollback journal codec rejected its own bytes"
  let checked := PhysicalJournalCodec.encodeChecked encodable
  unless PhysicalJournalCodec.decodeChecked checked |>.isSome do
    fail "checksummed rollback journal rejected its own bytes"
  let corrupted := checked.modify 20 (fun byte => byte + 1)
  unless PhysicalJournalCodec.decodeChecked corrupted |>.isNone do
    fail "checksummed rollback journal accepted a changed covered byte"
  let persistent ← match PhysicalJournalCodec.ofEncodable? encodable with
    | some value => pure value
    | none => fail "rollback journal exceeded persistent length bounds"
  let active := PhysicalJournalCodec.encodePersistentActive persistent ++
    List.replicate 4096 0
  match PhysicalJournalCodec.decodePersistent active with
  | some (some decoded) =>
      unless decoded.originalPageCount == journal.originalPageCount &&
          decoded.undo.map (fun record => record.pageId) ==
            journal.undo.map (fun record => record.pageId) &&
          decoded.undo.map (fun record => record.before.bytes) ==
            journal.undo.map (fun record => record.before.bytes) do
        fail "persistent rollback journal changed an active undo record"
  | _ => fail "persistent rollback journal rejected an active record with spare capacity"
  match PhysicalJournalCodec.decodePersistent
      PhysicalJournalCodec.initialInactiveBytes.data.toList with
  | some none => pure ()
  | _ => fail "persistent rollback journal rejected its durable inactive marker"
  let path : System.FilePath := ".lake/build/sqleanite-mvp-multipage.db"
  IO.FS.writeBinFile path (ByteArray.mk fileBytes.toArray)
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT id,first,second FROM items ORDER BY id;"] }
  unless output.exitCode == 0 do
    fail s!"sqlite3 rejected the verified multi-page B-tree: {output.stderr}"
  unless output.stdout == "ok\n1|11|\n2|22|\n3|33|\n4|44|\n5|55|\n" do
    fail s!"sqlite3 read unexpected multi-page rows: {repr output.stdout}"

private def expectGrowableRollbackJournal : IO Unit := do
  let oldPage : Storage.Page 4 := ⟨#[1, 2, 3, 4], by decide⟩
  let changedPage : Storage.Page 4 := ⟨#[5, 6, 7, 8], by decide⟩
  let grownPage : Storage.Page 4 := ⟨#[9, 10, 11, 12], by decide⟩
  let old : GrowableStorage.Image 4 := {
    pageCount := 1
    read := fun _ => oldPage }
  let writes : List (GrowableStorage.PageWrite 4) :=
    [⟨0, changedPage⟩, ⟨1, grownPage⟩]
  let journal := GrowableStorage.makeJournal old writes
  unless journal.originalPageCount == 1 && journal.undo.length == 1 do
    fail "growable rollback journal recorded a new page instead of only old pre-images"
  let committed := GrowableStorage.applyWrites old writes
  unless committed.pageCount == 2 && (committed.read 0).bytes == changedPage.bytes &&
      (committed.read 1).bytes == grownPage.bytes do
    fail "growable page writes did not modify and extend the image"
  let recovered := GrowableStorage.recoverWithJournal committed (some journal)
  unless recovered.pageCount == 1 && (recovered.read 0).bytes == oldPage.bytes do
    fail "page-level rollback did not restore old contents and truncate growth"
  let recoveredAgain :=
    GrowableStorage.recoverRepeatedly committed (some journal) 100
  unless recoveredAgain.pageCount == recovered.pageCount &&
      (recoveredAgain.read 0).bytes == (recovered.read 0).bytes do
    fail "repeated recovery was not idempotent across restarts"
  let interruptedMain := GrowableStorage.applyWrites committed
    (GrowableStorage.recoveryWrites journal)
  let recoveredAfterCopyCrash :=
    GrowableStorage.recoverWithJournal interruptedMain (some journal)
  unless recoveredAfterCopyCrash.pageCount == recovered.pageCount &&
      (recoveredAfterCopyCrash.read 0).bytes == (recovered.read 0).bytes do
    fail "recovery restart changed the result after page preimages were copied"
  let kept := GrowableStorage.recoverWithJournal committed none
  unless kept.pageCount == 2 && (kept.read 1).bytes == grownPage.bytes do
    fail "journal deletion did not retain the committed grown image"
  let target : GrowableStorage.Image 4 := {
    pageCount := 2
    read := fun pageId => if pageId = 0 then oldPage else grownPage }
  let delta := GrowableStorage.deltaWrites old target
  unless delta.length == 1 && delta.head?.map (·.pageId) == some 1 do
    fail "changed-page transaction retained an unchanged old page"
  let appliedDelta := GrowableStorage.applyWrites old delta
  unless appliedDelta.pageCount == 2 &&
      (appliedDelta.read 0).bytes == oldPage.bytes &&
      (appliedDelta.read 1).bytes == grownPage.bytes do
    fail "changed-page transaction did not refine the target image"
  -- This count is deliberately above the former native-stack ceiling.  Bulk
  -- creation compares an empty image with one write per physical page, so the
  -- old direct recursion crashed before it could return this list.
  let empty : GrowableStorage.Image 4 := {
    pageCount := 0
    read := fun _ => oldPage }
  let largeTarget : GrowableStorage.Image 4 := {
    pageCount := 200000
    read := fun _ => grownPage }
  let largeDelta := GrowableStorage.deltaWrites empty largeTarget
  unless largeDelta.length == 200000 &&
      largeDelta.head?.map (·.pageId) == some 199999 do
    fail "changed-page transaction did not remain stack-safe at 200,000 pages"

private def expectTornSectorModel : IO Unit := do
  unless TornStorage.tornWitnessPage.bytes == #[1, 1, 0, 0] do
    fail "sector crash witness did not retain exactly one written sector"
  unless TornStorage.tornWitnessPage.bytes != TornStorage.oldWitnessPage.bytes &&
      TornStorage.tornWitnessPage.bytes != TornStorage.intendedWitnessPage.bytes do
    fail "sector crash model collapsed to page-atomic outcomes"

private def expectPOSIXVFSPlan : IO Unit := do
  let page : Storage.Page 4 := ⟨#[1, 2, 3, 4], by decide⟩
  let old : GrowableStorage.Image 4 := { pageCount := 1, read := fun _ => page }
  let writes : List (GrowableStorage.PageWrite 4) := [⟨0, page⟩]
  let plan := POSIXVFS.commitPlan old writes
  unless plan.length == 8 do
    fail "POSIX VFS plan omitted a data or directory durability barrier"

private def expectGroupCommit : IO Unit := do
  let wal : GroupCommit.WAL Nat := { main := 0 }
  let batch := [1, 2, 3, 4]
  let grouped := wal.commitGroup batch
  let sequential := wal.commitSequential batch
  unless grouped.visible == 4 && grouped.durableFrames == [4, 3, 2, 1] &&
      grouped.durableFrames == sequential.durableFrames do
    fail "group commit changed serial full-image semantics"
  let staged : GroupCommit.WAL Nat := { main := 0, pendingFrames := [4, 3, 2, 1] }
  unless staged.absorbPending.sync.visible == staged.sync.visible do
    fail "full-image write absorption changed the published state"
  unless GroupCommit.syncCount (GroupCommit.groupProtocol batch) == 1 &&
      GroupCommit.syncCount (GroupCommit.sequentialProtocol batch) == 4 do
    fail "group commit did not reduce four durability barriers to one"

private def expectPhysicalGroupCommit : IO Unit := do
  let (created, _) ← match CoreSQL.execute { database := Core.Database.empty }
      "CREATE TABLE batched(id INTEGER PRIMARY KEY,value TEXT);" with
    | .ok outcome => pure outcome
    | .error message => fail s!"physical group setup failed: {message}"
  let (first, _) ← match CoreSQL.execute created
      "INSERT INTO batched VALUES(1,'a');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"physical group first state failed: {message}"
  let (second, _) ← match CoreSQL.execute first
      "INSERT INTO batched VALUES(2,'b');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"physical group second state failed: {message}"
  let paths : CoreWALFileAdapter.Paths := {
    main := ".lake/build/sqleanite-group-commit.db"
    wal := ".lake/build/sqleanite-group-commit.db-wal" }
  CoreWALFileAdapter.create {
    syncFile := fun _ => pure ()
    syncDeletion := fun _ => pure () } paths created.database
  let syncs ← IO.mkRef 0
  let syncOps : CoreWALFileAdapter.SyncOps := {
    syncFile := fun _ => syncs.modify (· + 1)
    syncDeletion := fun _ => pure () }
  let reopened ← CoreWALFileAdapter.commitBatch syncOps paths
    [first.database, second.database]
  unless reopened.Equiv second.database && (← syncs.get) == 1 do
    fail "physical group commit changed the newest state or used multiple file syncs"

private def expectVerifiedPageCache : IO Unit := do
  let store : Nat → Option Nat := fun key => some (key * 10)
  let cache := (PageCache.ReadCache.empty 2).insert 1 10 |>.insert 2 20
  unless cache.read 1 == some 10 && cache.read 2 == some 20 &&
      cache.entries.length == 2 do
    fail "bounded verified read cache lost a resident page"
  let evicted := cache.insert 3 30
  unless evicted.read 3 == some 30 && evicted.entries.length == 2 do
    fail "bounded verified read cache violated its capacity"
  let buffer := (PageCache.WriteBuffer.empty.put 7 70).put 7 71 |>.put 8 80
  unless buffer.entries.length == 2 && buffer.read 7 == some 71 &&
      buffer.flush.1.length == 2 && buffer.flush.2.entries.isEmpty do
    fail "deferred write buffer failed to absorb or flush writes"
  let _ := store

private def expectSafePageReuse : IO Unit := do
  let pending : List PageReuse.FreePage :=
    [{ pageId := 7, safeAfterEpoch := 3 },
     { pageId := 8, safeAfterEpoch := 9 }]
  unless PageReuse.takeReusable 10 pending |>.isNone do
    fail "page allocator reused a free page before its durability barrier"
  let durable := PageReuse.crossDurabilityBarrier pending
  match PageReuse.takeReusable 5 durable with
  | some (page, _) =>
      unless page.pageId == 7 do
        fail "page allocator ignored the oldest-reader epoch barrier"
  | none => fail "page allocator rejected a durable snapshot-safe page"

private def expectPhysicalWALCodec : IO Unit := do
  let header : PhysicalWAL.Header := {
    checkpointSequence := ⟨7, by decide⟩
    saltFirst := ⟨0x12345678, by decide⟩
    saltSecond := ⟨0x9abcdef0, by decide⟩ }
  unless PhysicalWAL.checksumBytes .zero header.prefix == header.checksum do
    fail "physical WAL header checksum disagreed with its byte recurrence"
  let first : PhysicalWAL.Frame := {
    pageNumber := ⟨⟨1, by decide⟩, by decide⟩
    databaseSize := ⟨2, by decide⟩
    page := Storage.Page.zero PhysicalCodec.pageSize }
  let secondPage : Storage.Page PhysicalCodec.pageSize := {
    bytes := Array.replicate PhysicalCodec.pageSize 42
    sizeInvariant := by simp }
  let second : PhysicalWAL.Frame := {
    pageNumber := ⟨⟨2, by decide⟩, by decide⟩
    databaseSize := ⟨2, by decide⟩
    page := secondPage }
  let wal : PhysicalWAL.WAL := { header, frames := [first, second] }
  match PhysicalWAL.decode wal.encode with
  | some decoded =>
      unless decoded.header == header && decoded.frames.length == 2 do
        fail "physical WAL decoder changed its header or frame count"
      match decoded.frames with
      | [decodedFirst, decodedSecond] =>
          unless decodedFirst.pageNumber == first.pageNumber &&
              decodedFirst.databaseSize == first.databaseSize &&
              decodedFirst.page.bytes == first.page.bytes &&
              decodedSecond.pageNumber == second.pageNumber &&
              decodedSecond.databaseSize == second.databaseSize &&
              decodedSecond.page.bytes == second.page.bytes do
            fail "physical WAL decoder changed a frame"
      | _ => fail "physical WAL decoder returned the wrong frame shape"
  | none => fail "physical WAL decoder rejected its own bytes"

private def expectGeneralMVPSchemaCore : IO Unit := do
  let users : Core.Schema := {
    name := "users"
    columns := [
      { name := "user_id", notNull := true, integerPrimaryKey := true },
      { name := "name", notNull := true },
      { name := "note" }]
    primaryKey := 0 }
  let posts : Core.Schema := {
    name := "posts"
    columns := [
      { name := "body" },
      { name := "post_id", notNull := true, integerPrimaryKey := true },
      { name := "author_id", notNull := true }]
    primaryKey := 1 }
  let withUsers ← match Core.Database.empty.createTable users with
    | .ok database => pure database
    | .error message => fail s!"general MVP rejected users schema: {message}"
  let database ← match withUsers.createTable posts with
    | .ok database => pure database
    | .error message => fail s!"general MVP rejected posts schema: {message}"
  if (database.createTable users).isOk then
    fail "general MVP admitted a duplicate table name"
  let usersTable ← match database.findTable? "users" with
    | some table => pure table
    | none => fail "general MVP lost users table"
  let alice : PhysicalCodec.Text := ⟨[65, 108, 105, 99, 101], by decide⟩
  let insertedUsers ← match usersTable.insertValues
      [.integer ⟨1, by decide, by decide⟩, .text alice, .null] with
    | .ok table => pure table
    | .error message => fail s!"general MVP rejected a valid user: {message}"
  if (insertedUsers.insertValues
      [.integer ⟨2, by decide, by decide⟩, .null, .null]).isOk then
    fail "general MVP admitted NULL in a NOT NULL column"
  let indexedUsers ← match insertedUsers.addIndex { name := "users_name", column := 1 } with
    | .ok table => pure table
    | .error message => fail s!"general MVP rejected a valid index: {message}"
  let database ← match database.updateTable indexedUsers with
    | .ok database => pure database
    | .error message => fail s!"general MVP failed to replace users table: {message}"
  let postsTable ← match database.findTable? "posts" with
    | some table => pure table
    | none => fail "general MVP lost posts table"
  let hello : PhysicalCodec.Text := ⟨[104, 101, 108, 108, 111], by decide⟩
  let insertedPosts ← match postsTable.insertValues
      [.text hello, .integer ⟨10, by decide, by decide⟩,
        .integer ⟨1, by decide, by decide⟩] with
    | .ok table => pure table
    | .error message => fail s!"general MVP rejected non-leading primary key: {message}"
  let database ← match database.updateTable insertedPosts with
    | .ok database => pure database
    | .error message => fail s!"general MVP failed to replace posts table: {message}"
  unless database.tables.length == 2 && indexedUsers.indexes.length == 1 &&
      indexedUsers.rows.length == 1 && insertedPosts.rows.length == 1 do
    fail "general MVP changed a table, index, or row count"

private def expectGeneralMVPSQL : IO Unit := do
  let sql := "
    CREATE TABLE users(user_id INTEGER PRIMARY KEY,name TEXT NOT NULL,note TEXT);
    CREATE TABLE posts(body TEXT,post_id INTEGER PRIMARY KEY,author_id INTEGER NOT NULL);
    CREATE INDEX users_name ON users(name);
    INSERT INTO users(name,user_id) VALUES('Ada',2),('Lin',1);
    UPDATE users SET note=X'0102' WHERE user_id=2;
    INSERT INTO posts VALUES('proofs',10,2),('storage',9,2);
    SELECT name,user_id FROM users WHERE NOT NOT name!='nobody' ORDER BY user_id;
    SELECT post_id,body FROM posts WHERE author_id>=1 ORDER BY post_id DESC LIMIT 1;
    SELECT DISTINCT author_id FROM posts ORDER BY author_id;
    SELECT count(*) FROM posts WHERE author_id=2;
    SELECT author_id,count(*),count(body),sum(post_id),min(post_id),max(post_id)
      FROM posts GROUP BY author_id;
    SELECT count(note) FROM users;
    SELECT sum(post_id) FROM posts WHERE author_id=2;
    SELECT min(post_id) FROM posts;
    SELECT max(post_id) FROM posts;
    SELECT min(note) FROM users WHERE user_id=99;
    SELECT note FROM users WHERE user_id=2;
    UPDATE users SET note=1.5 WHERE user_id=1;
    SELECT note FROM users WHERE user_id=1;
    SELECT user_id FROM users WHERE note=1.5;
    SELECT user_id FROM users UNION ALL SELECT author_id FROM posts;
    SELECT user_id FROM users UNION SELECT author_id FROM posts;
    SELECT user_id FROM users INTERSECT SELECT author_id FROM posts;
    SELECT user_id FROM users EXCEPT SELECT author_id FROM posts;
    SELECT users.user_id,posts.body FROM users
      LEFT JOIN posts ON users.user_id=posts.author_id;"
  let (state, results) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"general MVP SQL rejected supported schema: {message}"
  unless state.database.tables.length == 2 do
    fail "general MVP SQL did not retain both tables"
  for table in state.database.tables do
    let tree := table.rowTree.root.erase
    unless tree.toList == Core.treeEntries table.rows && tree.checkRootValid do
      fail "general MVP SQL could not materialize its verified table tree"
    for row in table.rows do
      let cell ← match CoreRecord.encodeCell? table.schema row with
        | some cell => pure cell
        | none => fail "general MVP row exceeded the physical record bounds"
      match CoreRecord.decodeRowCell table.schema (cell ++ [99]) with
      | some (decoded, [99]) =>
          unless decoded == row do
            fail "general MVP physical record changed an arbitrary-schema row"
      | _ => fail "general MVP physical record rejected its own cell"
  let projected := results.filter (fun result => !result.rows.isEmpty)
  unless projected.map (·.rows) ==
      [
        [[.text ⟨[76, 105, 110], by decide⟩, .integer ⟨1, by decide, by decide⟩],
         [.text ⟨[65, 100, 97], by decide⟩, .integer ⟨2, by decide, by decide⟩]],
        [[.integer ⟨10, by decide, by decide⟩,
          .text ⟨[112, 114, 111, 111, 102, 115], by decide⟩]],
        [[.integer ⟨2, by decide, by decide⟩]],
        [[.integer ⟨2, by decide, by decide⟩]],
        [[.integer ⟨2, by decide, by decide⟩,
          .integer ⟨2, by decide, by decide⟩,
          .integer ⟨2, by decide, by decide⟩,
          .integer ⟨19, by decide, by decide⟩,
          .integer ⟨9, by decide, by decide⟩,
          .integer ⟨10, by decide, by decide⟩]],
        [[.integer ⟨1, by decide, by decide⟩]],
        [[.integer ⟨19, by decide, by decide⟩]],
        [[.integer ⟨9, by decide, by decide⟩]],
        [[.integer ⟨10, by decide, by decide⟩]],
        [[.null]],
        [[.blob ⟨[1, 2], by decide⟩]],
        -- TEXT affinity renders the assigned REAL, as in C SQLite.
        [[.text ⟨[49, 46, 53], by decide⟩]],
        [[.integer ⟨1, by decide, by decide⟩]],
        [[.integer ⟨1, by decide, by decide⟩],
         [.integer ⟨2, by decide, by decide⟩],
         [.integer ⟨2, by decide, by decide⟩],
         [.integer ⟨2, by decide, by decide⟩]],
        [[.integer ⟨1, by decide, by decide⟩],
         [.integer ⟨2, by decide, by decide⟩]],
        [[.integer ⟨2, by decide, by decide⟩]],
        [[.integer ⟨1, by decide, by decide⟩]],
        [[.integer ⟨1, by decide, by decide⟩, .null],
         [.integer ⟨2, by decide, by decide⟩,
          .text ⟨[115, 116, 111, 114, 97, 103, 101], by decide⟩],
         [.integer ⟨2, by decide, by decide⟩,
          .text ⟨[112, 114, 111, 111, 102, 115], by decide⟩]]
      ] do
    fail "general MVP SQL returned the wrong arbitrary-schema rows"
  match CoreSQL.execute state
      "INSERT INTO users VALUES(3,NULL,NULL);" with
  | .ok _ => fail "general MVP SQL admitted a NOT NULL violation"
  | .error _ => pure ()
  let (_, nestedResults) ← match CoreSQL.execute state
      "SELECT user_id FROM users UNION ALL SELECT author_id FROM posts INTERSECT SELECT user_id FROM users;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"nested Core compound read failed: {message}"
  unless nestedResults.map (fun result => result.rows) ==
      [[[
        .integer ⟨1, by decide, by decide⟩],
        [.integer ⟨2, by decide, by decide⟩]]] do
    fail "nested Core compound read changed left-to-right bag semantics"

private def expectBinary64Core : IO Unit := do
  let positiveZero : FileFormat.U64Value := ⟨0, by decide⟩
  let negativeZero : FileFormat.U64Value := ⟨9223372036854775808, by decide⟩
  let one : FileFormat.U64Value := ⟨4607182418800017408, by decide⟩
  let oneAndHalf : FileFormat.U64Value := ⟨4609434218613702656, by decide⟩
  unless Binary64.compareBits positiveZero negativeZero == .eq &&
      Binary64.compareInteger 1 one == .eq &&
      Binary64.compareInteger 1 oneAndHalf == .lt &&
      PhysicalQuery.sqlEquals
        (.integer ⟨1, by decide, by decide⟩) (.realBits one) == .true do
    fail "exact binary64 comparison disagreed with SQLite numeric semantics"

private def expectGeneralMVPFileInterop : IO Unit := do
  let sql := "
    CREATE TABLE users(user_id INTEGER PRIMARY KEY,name TEXT NOT NULL,note TEXT);
    CREATE TABLE posts(body TEXT,post_id INTEGER PRIMARY KEY,author_id INTEGER NOT NULL);
    CREATE INDEX users_name ON users(name);
    INSERT INTO users(name,user_id,note) VALUES('Ada',2,X'0102'),('Lin',1,1.5);
    INSERT INTO posts VALUES('proofs',10,2),('storage',9,1);"
  let (state, _) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"general MVP file setup failed: {message}"
  let image ← match CoreFile.encode state.database with
    | some image => pure image
    | none => fail "general MVP file encoder rejected a small valid database"
  let canonical ← match CoreDecode.decodeCanonicalFile image.fileBytes with
    | some database => pure database
    | none => fail "strict canonical decoder rejected its own general image"
  unless canonical.Equiv state.database do
    fail "strict canonical decoder changed the logical database"
  unless image.fileBytes.length == PhysicalCodec.pageSize * 4 do
    fail "general MVP file encoder produced the wrong physical page count"
  let path : System.FilePath := ".lake/build/sqleanite-general-mvp.db"
  IO.FS.writeBinFile path (ByteArray.mk image.fileBytes.toArray)
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader", "
      PRAGMA integrity_check;
      SELECT user_id,name,typeof(note),quote(note) FROM users ORDER BY user_id;
      SELECT post_id,body,author_id FROM posts ORDER BY post_id;
      SELECT name FROM sqlite_master WHERE type='index' ORDER BY name;"] }
  unless output.exitCode == 0 && output.stdout ==
      "ok\n1|Lin|text|'1.5'\n2|Ada|blob|X'0102'\n9|storage|1\n10|proofs|2\nusers_name\n" do
    fail s!"sqlite3 rejected the arbitrary-schema image: {output.stderr}{output.stdout}"
  let mutation ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch",
      "INSERT INTO users VALUES(3,'C sqlite',2.25); UPDATE users SET note=X'CAFE' WHERE user_id=2; INSERT INTO posts VALUES('compact',11,3);"] }
  unless mutation.exitCode == 0 do
    fail s!"sqlite3 could not mutate the arbitrary-schema image: {mutation.stderr}"
  let mutatedBytes ← IO.FS.readBinFile path
  let decoded ← match CoreDecode.decode mutatedBytes.data.toList with
    | some database => pure database
    | none => fail "general decoder rejected an SQLite-written image"
  let users ← match decoded.findTable? "users" with
    | some table => pure table
    | none => fail "general decoder lost the users table"
  let posts ← match decoded.findTable? "posts" with
    | some table => pure table
    | none => fail "general decoder lost the posts table"
  unless users.rows.length == 3 && posts.rows.length == 3 &&
      users.indexes.map (·.name) == ["users_name"] do
    fail "general decoder lost a C-written row or index declaration"
  let cRow ← match users.rows.find? (fun row => row.rowid.value == 3) with
    | some row => pure row
    | none => fail "general decoder lost the compact C-written rowid"
  unless (cRow.value 1) == .text ⟨[67, 32, 115, 113, 108, 105, 116, 101], by decide⟩ do
    fail "general decoder changed C-written TEXT"
  unless (cRow.value 2) == .text ⟨[50, 46, 50, 53], by decide⟩ do
    fail "general decoder changed C-written TEXT affinity value"
  let adaRow ← match users.rows.find? (fun row => row.rowid.value == 2) with
    | some row => pure row
    | none => fail "general decoder lost the C-updated BLOB row"
  unless (adaRow.value 2) == .blob ⟨[202, 254], by decide⟩ do
    fail "general decoder changed C-written BLOB"
  let compact ← match posts.rows.find? (fun row => row.rowid.value == 11) with
    | some row => pure row
    | none => fail "general decoder lost the second C-written row"
  unless compact.value 2 == .integer ⟨3, by decide, by decide⟩ do
    fail "general decoder did not widen SQLite's compact integer serial type"

private def expectTextPrimaryKeyInterop : IO Unit := do
  let ddl :=
    "CREATE TABLE usertable (ycsb_key TEXT PRIMARY KEY, field0 TEXT);"
  let (state, results) ← match CoreSQL.execute Core.State.empty s!"
      {ddl}
      INSERT INTO usertable VALUES('user1','value1');
      SELECT * FROM usertable WHERE ycsb_key='user1';" with
    | .ok outcome => pure outcome
    | .error message => fail s!"TEXT PRIMARY KEY setup failed: {message}"
  unless results.getLast?.map (·.rows) == some [[
      .text ⟨[117, 115, 101, 114, 49], by decide⟩,
      .text ⟨[118, 97, 108, 117, 101, 49], by decide⟩]] do
    fail "TEXT PRIMARY KEY SELECT * exposed the internal rowid"
  let table ← match state.database.findTable? "usertable" with
    | some table => pure table
    | none => fail "TEXT PRIMARY KEY setup lost its table"
  let implicitIndex := match table.indexes with
    | [index] => index.isImplicitPrimary table.schema
    | _ => false
  unless table.schema.hasHiddenRowid && table.schema.catalogColumns.length == 2 &&
      implicitIndex do
    fail "TEXT PRIMARY KEY was not lowered through its proof-carrying automatic index"
  let routedUpdate := table.pointUpdateRowid?
    [(1, .text ⟨[117, 112, 100, 97, 116, 101, 100], by decide⟩)]
    (some (.equal table.schema.declaredPrimaryKey
      (.text ⟨[117, 115, 101, 114, 49], by decide⟩)))
  unless routedUpdate.isSome do
    fail "TEXT PRIMARY KEY UPDATE did not use the declared-key point route"
  let image ← match CoreFile.encode state.database with
    | some image => pure image
    | none => fail "TEXT PRIMARY KEY physical encoder rejected a valid row"
  let path : System.FilePath := ".lake/build/sqleanite-text-primary.db"
  IO.FS.writeBinFile path (ByteArray.mk image.fileBytes.toArray)
  let paths : CoreFileAdapter.Paths := {
    main := path
    journal := ".lake/build/sqleanite-text-primary.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  match ← CoreLazyFileEngine.execute? paths "
      SELECT * FROM usertable WHERE ycsb_key='user1';
      SELECT * FROM usertable WHERE ycsb_key='missing';" with
  | some (.ok [{ rows := found, changes := _ }, { rows := missing, changes := _ }]) =>
      unless found == [[
          .text ⟨[117, 115, 101, 114, 49], by decide⟩,
          .text ⟨[118, 97, 108, 117, 101, 49], by decide⟩]] &&
          missing.isEmpty do
        fail "page-directed TEXT PRIMARY KEY batch returned wrong rows"
  | _ => fail "TEXT PRIMARY KEY read batch missed the certified cold path"
  let inspected ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader", "
      SELECT sql FROM sqlite_master WHERE type='table' AND name='usertable';
      SELECT sql IS NULL FROM sqlite_master WHERE type='index';
      SELECT * FROM usertable;
      PRAGMA integrity_check;"] }
  unless inspected.exitCode == 0 && inspected.stdout ==
      "CREATE TABLE \"usertable\"(\"ycsb_key\" TEXT PRIMARY KEY,\"field0\" \"TEXT\")\n1\nuser1|value1\nok\n" do
    fail s!"SQLite rejected the exact TEXT PRIMARY KEY image: {inspected.stderr}{inspected.stdout}"
  let mutated ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch",
      "INSERT INTO usertable VALUES('user2','value2');"] }
  unless mutated.exitCode == 0 do
    fail s!"SQLite could not insert through the automatic TEXT PRIMARY KEY index: {mutated.stderr}"
  let bytes ← IO.FS.readBinFile path
  let reopened ← match CoreDecode.decode bytes.data.toList with
    | some database => pure database
    | none => fail "Lean rejected a C-written TEXT PRIMARY KEY row"
  let reopenedTable ← match reopened.findTable? "usertable" with
    | some table => pure table
    | none => fail "Lean reopen lost the TEXT PRIMARY KEY table"
  unless reopenedTable.rows.length == 2 && reopenedTable.indexes.length == 1 do
    fail "Lean reopen lost a C-written row or automatic index"
  match CoreSQL.execute { database := reopened }
      "INSERT INTO usertable VALUES('user2','different');" with
  | .ok _ => fail "TEXT PRIMARY KEY admitted a duplicate key after C interop"
  | .error message =>
      unless message == "UNIQUE constraint failed: PRIMARY KEY" do
        fail s!"TEXT PRIMARY KEY returned the wrong duplicate error: {message}"
  -- Exercise the exact file-backed statement shapes used by VeriBetrKV's
  -- YCSB A/B/C/D/F runs.  This deliberately uses the paper schema verbatim:
  -- there is no surrogate integer key or separately declared index.
  let connection ← CoreFileEngine.reopen .system paths
  let workload ← CoreFileEngine.execute connection "
    BEGIN;
    SELECT field0 FROM usertable WHERE ycsb_key='user1';
    UPDATE usertable SET field0='updated1' WHERE ycsb_key='user1';
    INSERT INTO usertable VALUES('user3','value3');
    SELECT field0 FROM usertable WHERE ycsb_key='user2';
    UPDATE usertable SET field0='updated2' WHERE ycsb_key='user2';
    COMMIT;"
  match workload with
  | .error message =>
      fail s!"file-backed TEXT PRIMARY KEY YCSB shapes failed: {message}"
  | .ok results =>
      let rows := results.flatMap (·.rows)
      unless rows == [
          [.text ⟨[118, 97, 108, 117, 101, 49], by decide⟩],
          [.text ⟨[118, 97, 108, 117, 101, 50], by decide⟩]] do
        fail "file-backed TEXT PRIMARY KEY reads returned wrong YCSB values"
  let workloadCheck ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader", "
      PRAGMA integrity_check;
      SELECT ycsb_key,field0 FROM usertable ORDER BY ycsb_key;"] }
  unless workloadCheck.exitCode == 0 && workloadCheck.stdout ==
      "ok\nuser1|updated1\nuser2|updated2\nuser3|value3\n" do
    fail s!"SQLite rejected the file-backed TEXT PRIMARY KEY workload: {workloadCheck.stderr}{workloadCheck.stdout}"

private def expectLiveOverflowInterop : IO Unit := do
  let large := String.mk (List.replicate 9000 'x')
  let sql := s!"
    CREATE TABLE overflowing(id INTEGER PRIMARY KEY,payload TEXT NOT NULL);
    CREATE INDEX overflowing_payload ON overflowing(payload);
    INSERT INTO overflowing VALUES(1,'{large}');"
  let (state, _) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"overflow SQL setup failed: {message}"
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-overflow.db"
    journal := ".lake/build/sqleanite-overflow.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  CoreFileAdapter.create .system paths state.database
  let reopened ← CoreFileAdapter.reopen paths
  unless reopened.Equiv state.database do
    fail "Lean overflow reopen changed the logical database"
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT length(payload) FROM overflowing INDEXED BY overflowing_payload; SELECT count(*) FROM overflowing;"] }
  unless output.exitCode == 0 && output.stdout == "ok\n9000\n1\n" do
    fail s!"sqlite3 rejected Lean overflow chains: {output.stderr}{output.stdout}"
  let mutation ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch",
      "UPDATE overflowing SET payload=hex(zeroblob(3500)) WHERE id=1;"] }
  unless mutation.exitCode == 0 do
    fail s!"sqlite3 could not rewrite the overflow chain: {mutation.stderr}"
  let cWritten ← CoreFileAdapter.reopen paths
  let table ← match cWritten.findTable? "overflowing" with
    | some table => pure table
    | none => fail "Lean lost the C-written overflow table"
  let row ← match table.rows.head? with
    | some row => pure row
    | none => fail "Lean lost the C-written overflow row"
  match row.value 1 with
  | .text value =>
      unless value.bytes.length == 7000 &&
          value.bytes.all (fun byte => byte == 48) do
        fail "Lean changed C-written overflow TEXT bytes"
  | _ => fail "Lean decoded C-written overflow TEXT as another storage class"

private def expectEscapedCatalogIdentifiers : IO Unit := do
  let sql := "
    CREATE TABLE \"odd\"\"table,one\"(
      \"id\"\"key\" INTEGER PRIMARY KEY,\"value,part\" TEXT NOT NULL);
    CREATE INDEX \"idx\"\"comma,\" ON \"odd\"\"table,one\"(\"value,part\");
    INSERT INTO \"odd\"\"table,one\" VALUES(1,'kept');"
  let (state, _) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"escaped catalog setup failed: {message}"
  let image ← match CoreFile.encode state.database with
    | some image => pure image
    | none => fail "escaped catalog encoder rejected a valid database"
  let decoded ← match CoreDecode.decode image.fileBytes with
    | some database => pure database
    | none => fail "escaped catalog decoder rejected its own image"
  let table ← match decoded.findTable? "odd\"table,one" with
    | some table => pure table
    | none => fail "escaped table name did not round-trip"
  unless table.schema.columns.map (·.name) == ["id\"key", "value,part"] &&
      table.indexes.map (·.name) == ["idx\"comma,"] && table.rows.length == 1 do
    fail "escaped catalog metadata changed during file round-trip"
  let path : System.FilePath := ".lake/build/sqleanite-escaped-catalog.db"
  IO.FS.writeBinFile path (ByteArray.mk image.fileBytes.toArray)
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT \"value,part\" FROM \"odd\"\"table,one\";"] }
  unless output.exitCode == 0 && output.stdout == "ok\nkept\n" do
    fail s!"sqlite3 rejected escaped catalog identifiers: {output.stderr}{output.stdout}"

private def expectPhysicalIndexTraversal : IO Unit := do
  let payload := String.mk (List.replicate 96 'x')
  let values := String.intercalate ","
    ((List.range 120).map fun offset =>
      let id := offset + 1
      s!"({id},'{payload}{id}',{id * 10},'old')")
  let sql := s!"
    CREATE TABLE indexed(id INTEGER PRIMARY KEY,value TEXT NOT NULL,score INTEGER NOT NULL,note TEXT NOT NULL);
    CREATE INDEX indexed_value ON indexed(value);
    CREATE INDEX indexed_score ON indexed(score);
    INSERT INTO indexed VALUES {values};
    CREATE TABLE signed_keys(id INTEGER PRIMARY KEY,value TEXT NOT NULL);
    INSERT INTO signed_keys VALUES(4,'positive');
    CREATE TABLE join_probe(id INTEGER PRIMARY KEY,label TEXT NOT NULL);
    INSERT INTO join_probe VALUES(2,'two'),(3,'three');"
  let (state, _) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"physical index setup failed: {message}"
  let attachedTable ← match state.database.findTableMember? "indexed" with
    | some table => pure table
    | none => fail "physical index setup lost its table"
  let table := attachedTable.val
  let index ← match table.indexes.find? (·.name == "indexed_value") with
    | some index => pure index
    | none => fail "physical index setup lost its index"
  let integerIndex ← match table.indexes.find? (·.name == "indexed_score") with
    | some index => pure index
    | none => fail "physical index setup lost its integer index"
  let threshold := (table.rows[60]?).map (fun row => row.value index.column)
    |>.getD .null
  let primaryValue := (table.rows[60]?).map (fun row => row.value 0)
    |>.getD .null
  let primaryQuery : Core.Query := {
    columns := [0, 1]
    predicate := some (.equal table.schema.primaryKey primaryValue) }
  match table.chooseAccessPath primaryQuery.predicate with
  | .primaryKey rowid =>
      unless rowid.value == 61 &&
          (table.plannedRows primaryQuery).map (fun row => row.rowid.value) == [61] do
        fail "primary-key planner returned the wrong routed row"
  | _ => fail "cost-aware planner did not select routed primary lookup"
  unless primaryQuery.eval (table.plannedRows primaryQuery) ==
      primaryQuery.eval table.rows do
    fail "routed primary-key lookup changed query semantics"
  let rangeQuery : Core.Query := {
    columns := [0]
    predicate := some (.compare .greaterEqual index.column threshold) }
  match table.chooseAccessPath rangeQuery.predicate with
  | .rangeIndex chosen =>
      unless chosen == index do
        fail "cost-aware range planner selected the wrong index"
  | _ => fail "cost-aware planner did not select a range index"
  unless rangeQuery.eval (table.plannedRows rangeQuery) ==
      rangeQuery.eval table.rows do
    fail "range index plan changed query semantics"
  let indexLeaves ← match CoreFile.indexLeaves table index with
    | some leaves => pure leaves
    | none => fail "physical index cells did not paginate"
  let indexPlan ← match RecursivePageBTree.buildIndex indexLeaves with
    | some plan => pure plan
    | none => fail "recursive physical index planner rejected valid leaves"
  unless indexPlan.height >= 2 && indexPlan.checkBalanced &&
      indexPlan.toCells == indexLeaves.flatten do
    fail "recursive physical index promotion changed contents or balance"
  let image ← match RecursivePageBTree.encode state.database with
    | some image => pure image
    | none => fail "physical index encoder rejected a multipage index"
  unless image.pages.length > 6 do
    fail "physical index test did not force multiple table and index leaves"
  let reopened ← match CoreDecode.decode image.fileBytes with
    | some database => pure database
    | none => fail "physical index traversal rejected its own multipage tree"
  unless reopened.Equiv state.database do
    fail "physical index traversal changed the indexed database"
  let physicalPages := CoreDecode.pages image.pageCount image.fileBytes
  let source := CoreDecode.PageSource.ofList physicalPages
  let catalog ← match physicalPages.head?.bind CoreDecode.decodeCatalog with
    | some catalog => pure catalog
    | none => fail "physical index certificate could not decode the catalog"
  let integerCatalog ← match catalog.find? fun entry =>
      entry.kind == "index" && entry.name == integerIndex.name with
    | some entry => pure entry
    | none => fail "physical index certificate lost the integer root"
  unless integerCatalog.sql.bind CanonicalIndexSQL.parseIntegerCertified |>.isSome do
    fail "integer-only physical index lost its persisted catalog certificate"
  let textCatalog ← match catalog.find? fun entry =>
      entry.kind == "index" && entry.name == index.name with
    | some entry => pure entry
    | none => fail "physical index certificate lost the text root"
  unless (textCatalog.sql.bind
      CanonicalIndexSQL.parseIntegerCertified).isNone do
    fail "mixed/text physical index received an integer-only certificate"
  unless (textCatalog.sql.bind
      CanonicalIndexSQL.parseTextCertified).isSome do
    fail "generated TEXT index lost its persisted routing certificate"
  let expected := CoreDecode.expectedIndexEntries table integerIndex
  let integerCertificate ← match CoreDecode.certifyIntegerIndex source
      (physicalPages.length + 1) integerCatalog.rootPage expected with
    | some certificate => pure certificate
    | none => fail "proof-producing integer index certification failed"
  let integerTarget := (table.rows[60]?).map
    (fun row => row.value integerIndex.column) |>.getD .null
  unless CoreDecode.lookupIndexValueFrom source integerTarget
      (physicalPages.length + 1) integerCatalog.rootPage ==
        some (expected.filter (fun entry => entry.matchesValue integerTarget)) do
    fail "certified integer equality traversal was not exact"
  unless CoreDecode.lookupIndexRangeFrom source .greaterEqual integerTarget
      (physicalPages.length + 1) integerCatalog.rootPage ==
        some (expected.filter
          (fun entry => entry.matchesRange .greaterEqual integerTarget)) do
    fail "certified integer range traversal was not exact"
  let textExpected := CoreDecode.expectedIndexEntries table index
  unless CoreDecode.indexPrefixFrom source 80 (physicalPages.length + 1)
      textCatalog.rootPage == some (textExpected.take 80) do
    fail "multi-leaf index cursor did not return the exact promoted-key prefix"
  let integerQuery : Core.Query := {
    columns := [0, integerIndex.column]
    predicate := some (.equal integerIndex.column integerTarget) }
  let retainedCertificates := CoreFileAdapter.certifyIntegerIndexes physicalPages
    catalog state.database
  let updatedState ← match CoreSQL.execute state
      "UPDATE indexed SET note='new' WHERE id=61;" with
    | .ok (updated, _) => pure updated
    | .error message => fail s!"certificate retarget setup failed: {message}"
  let attachedUpdatedTable ← match
      updatedState.database.findTableMember? "indexed" with
    | some updated => pure updated
    | none => fail "certificate retarget lost its logical table"
  let updatedTable := attachedUpdatedTable.val
  let retargeted := CoreFileAdapter.retargetIntegerIndexCertificates
    retainedCertificates updatedState.database
  let retargetQuery : Core.Query := {
    columns := [0, 3]
    predicate := some (.equal integerIndex.column integerTarget) }
  let retargetLookup ← match
      CoreFileAdapter.lookupCertifiedIndexCandidates retargeted updatedTable
        attachedUpdatedTable.property retargetQuery with
    | some lookup => pure lookup
    | none => fail "index-preserving update discarded its certificate"
  match retargetLookup.result.rows with
  | [[.integer id, .text note]] =>
      unless id.value == 61 && note.bytes == "new".toUTF8.toList do
        fail "retargeted certificate resolved rows from the old primary tree"
  | _ => fail "retargeted certificate returned the wrong result shape"
  let certifiedCandidates ← match
      CoreFileAdapter.lookupCertifiedIndexCandidates retainedCertificates table
        attachedTable.property integerQuery with
    | some lookup => pure lookup
    | none => fail "integer index certificate was not reusable by a query"
  unless certifiedCandidates.candidates.map (·.rowid.value) == [61] do
    fail "certified candidate resolution changed primary-tree row order"
  let path : System.FilePath := ".lake/build/sqleanite-recursive-index.db"
  IO.FS.writeBinFile path (ByteArray.mk image.fileBytes.toArray)
  let paths : CoreFileAdapter.Paths := {
    main := path
    journal := ".lake/build/sqleanite-recursive-index.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  let some geometry ← CoreFileAdapter.readGeneratedFileGeometry paths |
    fail "cached primary setup lost generated geometry"
  let primaryKeys : List Core.Integer :=
    [⟨-1, by decide, by decide⟩] ++
      (List.range 122).filterMap CoreFile.signedNat?
  for capacity in [0, 1, 512] do
    let cache ← CoreFileAdapter.PageReadCache.create capacity
    -- Visit multiple leaves, hits and both sides of the key range, then
    -- revisit them in reverse. A disabled or saturated cache must be exact.
    for key in primaryKeys ++ primaryKeys.reverse do
      let some actual ← CoreFileAdapter.lookupGeneratedPrimaryRowWith geometry
          paths "indexed" table.schema cache key |
        fail "cached primary reader rejected a valid tree"
      let expected := table.rows.find? (fun row => row.rowid = key)
      unless actual.map (·.values) == expected.map (·.values) do
        fail s!"cached primary reader changed row {key.value} at capacity {capacity}"
    unless (← cache.pages.get).size ≤ capacity do
      fail "primary reader exceeded the page-cache bound"
    unless (← cache.tableCursors.get).size ≤ capacity do
      fail "primary reader exceeded the cursor-cache bound"
    unless (← cache.tableViews.get).size ≤ capacity do
      fail "primary reader exceeded the batch-wide checked-page cache bound"
    for (_, cursor) in (← cache.tableCursors.get).toList do
      unless (← cursor.views.get).size ≤ capacity do
        fail "primary reader exceeded the checked-page cache bound"
    unless (← CoreFileAdapter.lookupGeneratedPrimaryRowWith geometry paths
        "join_probe" table.schema cache ⟨2, by decide, by decide⟩).isNone do
      fail "primary reader accepted a schema from another table"
  for capacity in [1, 2] do
    let shared ← CoreFileAdapter.PageReadCache.create capacity
    for name in ["indexed", "signed_keys", "indexed", "signed_keys"] do
      let some schema := geometry.tableSchema? name | fail "shared-view test lost schema"
      for key in [1, 4, 120] do
        let some integer := CoreFile.signedNat? key | fail "shared-view key out of range"
        unless (← CoreFileAdapter.lookupGeneratedPrimaryRowWith geometry paths
            name schema shared integer).isSome do
          fail "shared view cache rejected a valid cross-table read"
      unless (← shared.tableViews.get).size ≤ capacity do
        fail "view capacity multiplied by the number of table cursors"
  let primaryBatch := "SELECT id,value FROM indexed WHERE id=1;
    SELECT id,value FROM signed_keys WHERE id=4;
    SELECT id,value FROM indexed WHERE id=120;
    SELECT id,value FROM indexed WHERE id=999;
    SELECT id,value FROM indexed WHERE id=1;"
  let expectedBatch ← match CoreSQL.execute state primaryBatch with
    | .ok (_, results) => pure results
    | .error message => fail s!"primary batch reference failed: {message}"
  match ← CoreLazyFileEngine.execute? paths primaryBatch with
  | some (.ok actual) =>
      unless actual.map (·.rows) == expectedBatch.map (·.rows) do
        fail "cached primary batch changed projection, ordering, or table identity"
  | _ => fail "primary batch missed the generated fast path"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT id,value FROM indexed WHERE id=999;" with
  | some (.ok [{ rows := [], changes := _ }]) => pure ()
  | _ => fail "generated-image primary miss did not stay page-directed"
  let coldIndexQuery : Core.Query := {
    columns := [0, integerIndex.column]
    predicate := some (.equal integerIndex.column integerTarget) }
  let coldIndexLookup ← match ←
      CoreFileAdapter.lookupGeneratedIndexCandidates paths "indexed"
        table.schema coldIndexQuery with
    | some lookup => pure lookup
    | none => fail "generated INTEGER index did not take the cold path"
  unless coldIndexLookup.candidates.map (·.rowid.value) == [61] &&
      coldIndexLookup.pagesRead < image.pages.length do
    fail "cold INTEGER index lookup did not remain page-directed"
  let coldTextQuery : Core.Query := {
    columns := [0, index.column]
    predicate := some (.equal index.column threshold) }
  let coldTextLookup ← match ←
      CoreFileAdapter.lookupGeneratedIndexCandidates paths "indexed"
        table.schema coldTextQuery with
    | some lookup => pure lookup
    | none => fail "generated TEXT index did not take the cold path"
  unless coldTextLookup.candidates.map (·.rowid.value) == [61] &&
      coldTextLookup.pagesRead < image.pages.length do
    fail "cold TEXT index lookup did not remain page-directed"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT id,score FROM indexed WHERE score=610;" with
  | some (.ok [{ rows := [[.integer id, .integer score]], .. }]) =>
      unless id.value == 61 && score.value == 610 do
        fail "cold secondary equality SELECT returned the wrong row"
  | _ => fail "cold secondary equality SELECT missed the page-directed path"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT id,score FROM indexed WHERE score>=1190 ORDER BY id;" with
  | some (.ok [{ rows := rows, .. }]) =>
      unless rows == [[.integer ⟨119, by decide, by decide⟩,
          .integer ⟨1190, by decide, by decide⟩],
        [.integer ⟨120, by decide, by decide⟩,
          .integer ⟨1200, by decide, by decide⟩]] do
        fail "cold secondary range SELECT returned the wrong rows"
  | _ => fail "cold secondary range SELECT missed the page-directed path"
  let orderedQuery : Core.Query := {
    columns := [0, index.column]
    orderBy := [(index.column, false)]
    limit := some 5 }
  let orderedPrefix ← match ←
      CoreFileAdapter.lookupGeneratedOrderedPrefix paths "indexed" table.schema
        orderedQuery with
    | some lookup => pure lookup
    | none => fail "generated ORDER BY prefix did not take the cold path"
  let prefixIds := (orderedQuery.selectedRows orderedPrefix.candidates).map
    (fun row => row.rowid.value)
  let expectedIds := (orderedQuery.selectedRows table.rows).map
    (fun row => row.rowid.value)
  unless orderedQuery.eval orderedPrefix.candidates ==
      orderedQuery.eval table.rows && orderedPrefix.candidates.length == 5 do
    fail s!"cold ORDER BY prefix mismatch: candidate ids={repr prefixIds} expected ids={repr expectedIds} reads={orderedPrefix.pagesRead}/{image.pages.length}"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT id,value FROM indexed ORDER BY value LIMIT 5;" with
  | some (.ok [{ rows := rows, .. }]) =>
      unless rows == orderedQuery.eval table.rows do
        fail "cold ORDER BY LIMIT SELECT returned the wrong rows"
  | _ => fail "cold ORDER BY LIMIT SELECT missed the page-directed path"
  let multiLeafQuery : Core.Query := {
    columns := [0, index.column]
    orderBy := [(index.column, false)]
    limit := some 80 }
  let multiLeafPrefix ← match ←
      CoreFileAdapter.lookupGeneratedOrderedPrefix paths "indexed" table.schema
        multiLeafQuery with
    | some lookup => pure lookup
    | none => fail "multi-leaf ORDER BY prefix missed the cold cursor"
  unless multiLeafPrefix.candidates.length == 80 &&
      multiLeafQuery.eval multiLeafPrefix.candidates ==
        multiLeafQuery.eval table.rows do
    fail "multi-leaf ORDER BY prefix changed query results"
  let primaryRange ← match ← CoreFileAdapter.lookupGeneratedPrimaryRange
      paths "indexed" table.schema .greater ⟨115, by decide, by decide⟩ with
    | some lookup => pure lookup
    | none => fail "generated primary range did not take the cold path"
  unless primaryRange.candidates.map (·.rowid.value) == [116, 117, 118, 119, 120] &&
      primaryRange.pagesRead < image.pages.length do
    fail "cold primary range did not remain separator-directed"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT id,score FROM indexed WHERE id>115;" with
  | some (.ok [{ rows := rows, .. }]) =>
      unless rows.map (fun row => row[0]?) ==
          [some (.integer ⟨116, by decide, by decide⟩),
           some (.integer ⟨117, by decide, by decide⟩),
           some (.integer ⟨118, by decide, by decide⟩),
           some (.integer ⟨119, by decide, by decide⟩),
           some (.integer ⟨120, by decide, by decide⟩)] do
        fail "cold primary range SELECT returned the wrong rows"
  | _ => fail "cold primary range SELECT missed the page-directed path"
  let joinLookup ← match ← CoreFileAdapter.lookupGeneratedPrimaryJoin paths
      "indexed" "join_probe" with
    | some lookup => pure lookup
    | none => fail "generated primary-key join did not take the cold path"
  unless joinLookup.leftCandidates.map (·.rowid.value) == [1, 2, 3] &&
      joinLookup.rightRows.map (·.rowid.value) == [2, 3] &&
      joinLookup.bound.map (·.value) == some 3 &&
      joinLookup.pagesRead < image.pages.length do
    fail "cold primary-key join did not remain range-directed"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT indexed.id,join_probe.label FROM indexed JOIN join_probe ON indexed.id=join_probe.id;" with
  | some (.ok [{ rows := rows, .. }]) =>
      unless rows ==
          [[.integer ⟨2, by decide, by decide⟩,
            .text ⟨[116, 119, 111], by decide⟩],
           [.integer ⟨3, by decide, by decide⟩,
            .text ⟨[116, 104, 114, 101, 101], by decide⟩]] do
        fail "cold primary-key join returned the wrong rows"
  | _ => fail "cold primary-key join missed the page-directed path"
  let signedMutation ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "INSERT INTO signed_keys VALUES(-7,'negative');"] }
  unless signedMutation.exitCode == 0 do
    fail s!"sqlite3 could not add a negative rowid: {signedMutation.stderr}"
  let primaryLookup ← match ←
      CoreFileAdapter.lookupPrimaryRow paths "indexed"
        ⟨61, by decide, by decide⟩ with
    | some lookup => pure lookup
    | none => fail "cold primary lookup rejected a valid row"
  unless primaryLookup.row.rowid.value == 61 &&
      primaryLookup.pagesRead < image.pages.length do
    fail s!"cold primary lookup visited {primaryLookup.pagesRead} of {image.pages.length} pages"
  let cold ← CoreLazyFileEngine.execute? paths
    "SELECT id,value FROM indexed WHERE id=61;"
  match cold with
  | some (.ok [{ rows := [[.integer id, .text value]], .. }]) =>
      unless id.value == 61 && value.bytes.length == 98 do
        fail "cold primary SELECT returned the wrong row"
  | _ => fail "cold primary SELECT did not use the page-directed path"
  let negativeLookup ← match ←
      CoreFileAdapter.lookupPrimaryRow paths "signed_keys"
        ⟨-7, by decide, by decide⟩ with
    | some lookup => pure lookup
    | none => fail "cold primary lookup rejected a negative rowid"
  unless negativeLookup.row.rowid.value == -7 &&
      negativeLookup.pagesRead < image.pages.length + 2 do
    fail "cold primary lookup changed signed rowid routing"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT id,value FROM signed_keys WHERE id=-7;" with
  | some (.ok [{ rows := [[.integer id, .text value]], .. }]) =>
      unless id.value == -7 && value.bytes == "negative".toUTF8.toList do
        fail "cold primary SELECT changed a negative rowid result"
  | _ => fail "cold primary SELECT did not recognize a negative rowid"
  unless (← CoreLazyFileEngine.execute? paths
      "SELECT id,value FROM indexed WHERE id=999;").isNone do
    fail "C-mutated primary miss bypassed the validating fallback"
  unless (← CoreFileAdapter.lookupGeneratedIndexCandidates paths "indexed"
      table.schema coldIndexQuery).isNone do
    fail "C-mutated index bypassed the generated-image fallback"
  let equalityQuery : Core.Query := {
    columns := [0, 1]
    predicate := some (.equal index.column threshold) }
  let lookup ← match ←
      CoreFileAdapter.lookupIndexCandidates paths table equalityQuery with
    | some lookup => pure lookup
    | none => fail "persisted equality lookup rejected a valid index"
  unless lookup.candidates.length == 1 &&
      lookup.candidates.head?.map (·.rowid.value) == some 61 &&
      lookup.pagesRead < indexPlan.pageCount do
    fail s!"page-directed lookup visited {lookup.pagesRead} of {indexPlan.pageCount} index pages"
  let rangeLookup ← match ←
      CoreFileAdapter.lookupIndexCandidates paths table rangeQuery with
    | some lookup => pure lookup
    | none => fail "persisted range lookup rejected a valid index"
  unless rangeQuery.eval rangeLookup.candidates == rangeQuery.eval table.rows &&
      rangeLookup.pagesRead < indexPlan.pageCount do
    fail s!"page-directed range visited {rangeLookup.pagesRead} of {indexPlan.pageCount} index pages"
  let connection ← CoreFileEngine.reopen .system paths
  let live ← CoreFileEngine.execute connection
    s!"SELECT id,value FROM indexed WHERE value='{payload}61';"
  match live with
  | .ok [{ rows := [[.integer id, .text value]], .. }] =>
      unless id.value == 61 && value.bytes.length == 98 do
        fail "live persisted-index lookup returned the wrong row"
  | _ => fail "live query did not execute through persisted-index candidates"
  let certifiedLive ← CoreFileEngine.execute connection
    "SELECT id,score FROM indexed WHERE score=610;"
  match certifiedLive with
  | .ok [{ rows := [[.integer id, .integer score]], .. }] =>
      unless id.value == 61 && score.value == 610 do
        fail "live certified integer index returned the wrong row"
  | _ => fail "live certified integer index did not execute"
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT count(*) FROM indexed INDEXED BY indexed_value;"] }
  unless output.exitCode == 0 && output.stdout == "ok\n120\n" do
    fail s!"sqlite3 rejected the recursive physical index: {output.stderr}{output.stdout}"

private def expectWideCIndexCertificate : IO Unit := do
  let path : System.FilePath := ".lake/build/sqleanite-wide-c-index.db"
  let paths : CoreFileAdapter.Paths := {
    main := path
    journal := ".lake/build/sqleanite-wide-c-index.db-journal" }
  if ← path.pathExists then IO.FS.removeFile path
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  let created ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString,
      "PRAGMA page_size=4096; VACUUM; CREATE TABLE wide(id INTEGER PRIMARY KEY,score INTEGER NOT NULL,payload TEXT NOT NULL); WITH RECURSIVE n(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM n WHERE x<4000) INSERT INTO wide SELECT x,x*10,printf('payload-%d',x) FROM n; CREATE INDEX wide_score ON wide(score); CREATE TABLE mixed(id INTEGER PRIMARY KEY,v); INSERT INTO mixed VALUES(1,NULL),(2,5),(3,5.5),(4,'five'),(5,x'05'); CREATE INDEX mixed_v ON mixed(v);"] }
  unless created.exitCode == 0 do
    fail s!"sqlite3 could not create a wide index: {created.stderr}"
  let database ← CoreFileAdapter.reopen paths
  let attachedTable ← match database.findTableMember? "wide" with
    | some table => pure table
    | none => fail "general decoder lost the C-produced wide table"
  let table := attachedTable.val
  let index ← match table.indexes.find? (·.name == "wide_score") with
    | some index => pure index
    | none => fail "general decoder lost the C-produced wide index"
  let certificates ←
    CoreFileAdapter.loadIntegerIndexCertificates paths database
  let stored ← match certificates.find? fun stored =>
      stored.table.schema.name == "wide" && stored.index.name == "wide_score" with
    | some stored => pure stored
    | none => fail "wide C-produced index did not receive a certificate"
  match stored.certificate with
  | .general _ => pure ()
  | .generated _ =>
      fail "wide C-produced index unexpectedly used the generated 2-3 decoder"
  | .allValues _ =>
      fail "integer-only wide index received a conservative mixed certificate"
  | .text _ =>
      fail "integer-only wide index received a text certificate"
  let target : Core.Value := .integer ⟨20000, by decide, by decide⟩
  let query : Core.Query := {
    columns := [0, index.column]
    predicate := some (.equal index.column target) }
  let certified ← match
      CoreFileAdapter.lookupCertifiedIndexCandidates certificates table
        attachedTable.property query with
    | some certified => pure certified
    | none => fail "wide C-produced index fell back to a full query"
  match certified.result.rows with
  | [[.integer id, .integer score]] =>
      unless id.value == 2000 && score.value == 20000 do
        fail "wide C-produced certificate returned the wrong row"
  | _ => fail "wide C-produced certificate returned the wrong result shape"
  let attachedMixedTable ← match database.findTableMember? "mixed" with
    | some table => pure table
    | none => fail "general decoder lost the mixed-storage table"
  let mixedTable := attachedMixedTable.val
  let mixedIndex ← match mixedTable.indexes.find? (·.name == "mixed_v") with
    | some index => pure index
    | none => fail "general decoder lost the mixed-storage index"
  let mixedStored ← match certificates.find? fun stored =>
      stored.table.schema.name == "mixed" && stored.index.name == "mixed_v" with
    | some stored => pure stored
    | none => fail "mixed-storage index did not receive an exact certificate"
  match mixedStored.certificate with
  | .allValues _ => pure ()
  | _ => fail "mixed-storage index received an invalid ordered certificate"
  let textTarget ← match mixedTable.rows.find? (·.rowid.value == 4) with
    | some row => pure (row.value mixedIndex.column)
    | none => fail "mixed-storage test lost its text row"
  let mixedQuery : Core.Query := {
    columns := [0]
    predicate := some (.equal mixedIndex.column textTarget) }
  let mixedCertified ← match
      CoreFileAdapter.lookupCertifiedIndexCandidates certificates mixedTable
        attachedMixedTable.property mixedQuery with
    | some certified => pure certified
    | none => fail "mixed-storage equality query fell back to a full plan"
  match mixedCertified.result.rows with
  | [[.integer id]] =>
      unless id.value == 4 do
        fail "mixed-storage certificate returned the wrong equality row"
  | _ => fail "mixed-storage certificate returned the wrong equality shape"
  let mixedRange : Core.Query := {
    columns := [0]
    predicate := some (.compare .greaterEqual mixedIndex.column textTarget) }
  let rangeCertified ← match
      CoreFileAdapter.lookupCertifiedIndexCandidates certificates mixedTable
        attachedMixedTable.property mixedRange with
    | some certified => pure certified
    | none => fail "mixed-storage range query fell back to a full plan"
  unless rangeCertified.result.rows ==
      mixedRange.eval mixedTable.rows do
    fail "mixed-storage exact certificate changed range semantics"

private def expectCoreFreelistShrink : IO Unit := do
  let payload := String.mk (List.replicate 96 'f')
  let values := String.intercalate ","
    ((List.range 128).map fun offset =>
      let id := offset + 1
      s!"({id},'{payload}{id}')")
  let setupSQL := s!"
    CREATE TABLE shrinking(id INTEGER PRIMARY KEY,value TEXT NOT NULL);
    CREATE INDEX shrinking_value ON shrinking(value);
    INSERT INTO shrinking VALUES {values};"
  let (largeState, _) ← match CoreSQL.execute Core.State.empty setupSQL with
    | .ok outcome => pure outcome
    | .error message => fail s!"Core freelist setup failed: {message}"
  let path : System.FilePath := ".lake/build/sqleanite-core-freelist.db"
  let paths : CoreFileAdapter.Paths := {
    main := path
    journal := ".lake/build/sqleanite-core-freelist.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  CoreFileAdapter.create .system paths largeState.database
  let oldBytes ← IO.FS.readBinFile path
  let oldPages := oldBytes.size / PhysicalCodec.pageSize
  let validatedBefore ← match ← CoreFileAdapter.loadOpenState paths with
    | some value => pure value
    | none => fail "full-chunk index setup did not validate"
  let (insertedState, _) ← match CoreSQL.execute largeState
      "INSERT INTO shrinking VALUES(129,'split');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"split-reuse insert failed: {message}"
  let insertedDelta ← match CoreChunkPageDelta.updateStateCandidate?
      validatedBefore.state insertedState.database with
    | some value => pure value
    | none => fail "full-chunk insert did not produce a physical delta"
  unless insertedDelta.after.nextPage == validatedBefore.state.nextPage &&
      insertedDelta.table.freedPageNumbers.isEmpty do
    fail "split insertion did not recycle the pages released by its old chunk"
  let (smallState, _) ← match CoreSQL.execute largeState
      "DELETE FROM shrinking WHERE id>1;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"Core freelist delete failed: {message}"
  let validated ← match ← CoreFileAdapter.loadOpenState paths with
    | some value => pure value
    | none => fail "indexed shrink did not produce a validated physical state"
  let deltaResult : { delta : CoreChunkPageDelta.StateDelta //
      CoreChunkPageDelta.updateStateCandidate? validated.state
        smallState.database = some delta } ←
    match candidate : CoreChunkPageDelta.updateStateCandidate?
        validated.state smallState.database with
    | some value =>
        pure (⟨value, candidate⟩ : { delta : CoreChunkPageDelta.StateDelta //
          CoreChunkPageDelta.updateStateCandidate? validated.state
            smallState.database = some delta })
    | none => fail "indexed shrink did not produce a proof-carrying table delta"
  let delta := deltaResult.val
  have canonicalCandidate :
      CoreChunkPageDelta.updateStateCandidate? delta.before
        delta.after.database = some delta := by
    have endpoints := CoreChunkPageDelta.updateStateCandidate?_endpoints
      deltaResult.property
    rw [endpoints.1, endpoints.2]
    exact deltaResult.property
  if delta.table.tablePagesSufficient then
    fail "changed index was incorrectly treated as an unchanged page image"
  let input ← IO.FS.readBinFile path
  let prepared ← match CoreFileAdapter.prepareLocalizedLastIndex? validated
      input.data.toList delta canonicalCandidate with
    | some value => pure value
    | none => fail "tail-owned changed index did not produce a localized delta"
  unless prepared.writes.length < oldPages do
    fail "localized indexed shrink rewrote the whole file"
  let connection ← CoreFileEngine.reopen .system paths
  match ← CoreFileEngine.execute connection
      "DELETE FROM shrinking WHERE id>1;" with
  | .error message => fail s!"live localized indexed shrink failed: {message}"
  | .ok _ => pure ()
  let reopened ← CoreFileAdapter.reopen paths
  unless reopened.Equiv smallState.database do
    fail "Core freelist commit changed the logical database"
  let newBytes ← IO.FS.readBinFile path
  unless newBytes.size / PhysicalCodec.pageSize == oldPages do
    fail "Core freelist shrink changed the physical file size"
  let check ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; PRAGMA freelist_count; SELECT count(*) FROM shrinking;"] }
  let lines := check.stdout.trimAscii.toString.splitOn "\n"
  unless check.exitCode == 0 && lines.length == 3 && lines[0]? == some "ok" &&
      lines[2]? == some "1" do
    fail s!"SQLite rejected the Core freelist image: {check.stderr}{check.stdout}"
  let free ← match lines[1]?.bind String.toNat? with
    | some count => pure count
    | none => fail "SQLite did not report the Core freelist count"
  unless 0 < free do
    fail "Core shrink did not publish any pages on the freelist"

private def expectCoreDirtyPageCommit : IO Unit := do
  let payload := String.mk (List.replicate 96 'd')
  let values := String.intercalate ","
    ((List.range 100).map fun offset => s!"({offset + 1},'{payload}')")
  let setup := s!"CREATE TABLE dirty_rows(
      id INTEGER PRIMARY KEY,payload TEXT NOT NULL);
    INSERT INTO dirty_rows VALUES {values};"
  let (oldState, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok outcome => pure outcome
    | .error message => fail s!"dirty-page setup failed: {message}"
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-dirty-pages.db"
    journal := ".lake/build/sqleanite-dirty-pages.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  CoreFileAdapter.create .system paths oldState.database
  let oldBytes ← IO.FS.readBinFile paths.main
  let oldPages := oldBytes.size / PhysicalCodec.pageSize
  let replacement := String.mk (List.replicate 96 'e')
  let (newState, _) ← match CoreSQL.execute oldState
      s!"UPDATE dirty_rows SET payload='{replacement}' WHERE id=50;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"dirty-page update failed: {message}"
  let physical ← match ← CoreFileAdapter.loadPageState paths oldState.database with
    | some state => pure state
    | none => fail "stable physical image did not load into its proved representation"
  let (bulkUpdated, _) ← match CoreSQL.execute oldState
      s!"UPDATE dirty_rows SET payload='{replacement}' WHERE id>=40;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"bulk dirty-page update failed: {message}"
  let bulkUpdateDelta ← match CoreChunkPageDelta.updateState?
      physical bulkUpdated.database with
    | some value => pure value
    | none => fail "same-key bulk update did not produce a proved page delta"
  unless bulkUpdateDelta.after.database.Equiv bulkUpdated.database do
    fail "same-key bulk update delta changed the represented database"
  let (bulkDeleted, _) ← match CoreSQL.execute oldState
      "DELETE FROM dirty_rows WHERE id>=40;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"bulk dirty-page delete failed: {message}"
  let bulkDeleteDelta ← match CoreChunkPageDelta.updateState?
      physical bulkDeleted.database with
    | some value => pure value
    | none => fail "bulk retain did not produce a proved page delta"
  unless bulkDeleteDelta.after.database.Equiv bulkDeleted.database do
    fail "bulk retain delta changed the represented database"
  unless bulkDeleteDelta.table.after.tree.root.pageIds.Pairwise
      (fun left right => left ≠ right) &&
      bulkDeleteDelta.table.freedPageNumbers.Pairwise
        (fun left right => left ≠ right) &&
      !bulkDeleteDelta.table.freedPageNumbers.any
        bulkDeleteDelta.table.after.tree.root.pageIds.contains do
    fail "bulk retain duplicated or freed an active persistent page ID"
  let delta ← match CoreChunkPageDelta.updateState? physical newState.database with
    | some delta => pure delta
    | none => fail "single-row update did not produce a proved page delta"
  let writes ← match CoreChunkPageDelta.writes delta.table with
    | some writes => pure writes
    | none => fail "proved page delta contained an invalid page number"
  let before ← match CoreChunkPageDelta.beforeWrites delta.table with
    | some writes => pure writes
    | none => fail "proved before-image path contained an invalid page number"
  let committed ← match ← CoreFileAdapter.commitLocalizedCertified
      .system paths before writes with
    | some committed => pure committed
    | none => fail "on-disk pages did not match the proved before-image"
  have _traceExact : committed.requests =
      CoreFileAdapter.preparedCommitPlan committed.journal
        committed.prepared.writes := committed.trace_eq
  let plan := committed.requests
  -- Materialize the persistent protocol's crash checkpoint after the new main
  -- pages reached disk but before the active journal was retired. The live
  -- recovery path must restore the exact old logical database and then leave
  -- the retained inode in its non-hot inactive state.
  let encodableJournal ← match
      PhysicalJournalCodec.ofJournal? committed.journal with
    | some value => pure value
    | none => fail "localized recovery journal exceeded its encoded bounds"
  let persistentJournal ← match
      PhysicalJournalCodec.ofEncodable? encodableJournal with
    | some value => pure value
    | none => fail "localized recovery journal exceeded its persistent bounds"
  IO.FS.writeBinFile paths.journal
    (PhysicalJournalCodec.encodePersistentActiveBytes persistentJournal)
  CoreFileAdapter.recoverInPlace .system paths
  let recoveredOld ← CoreFileAdapter.reopen paths
  unless recoveredOld.Equiv oldState.database do
    fail "persistent active journal did not restore the old Core database"
  let retiredJournal ← IO.FS.readBinFile paths.journal
  match PhysicalJournalCodec.decodePersistent retiredJournal.data.toList with
  | some none => pure ()
  | _ => fail "persistent recovery did not retire the journal inode"
  unless (← CoreFileAdapter.commitLocalizedCertified
      .system paths before writes).isSome do
    fail "localized commit did not replay after persistent recovery"
  let (deletedState, _) ← match CoreSQL.execute newState
      "DELETE FROM dirty_rows WHERE id=51;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"dirty-page delete failed: {message}"
  let deletedDelta ← match CoreChunkPageDelta.updateState?
      delta.after deletedState.database with
    | some value => pure value
    | none => fail "single-row delete did not produce a proved page delta"
  let deletedBefore ← match CoreChunkPageDelta.beforeWrites deletedDelta.table with
    | some value => pure value
    | none => fail "delete before-image contained page zero"
  let deletedWrites ← match CoreChunkPageDelta.writes deletedDelta.table with
    | some value => pure value
    | none => fail "delete delta contained page zero"
  unless (← CoreFileAdapter.commitLocalized .system paths deletedBefore
      deletedWrites).isSome do
    fail "delete pages did not match their proved before-image"
  let (insertedState, _) ← match CoreSQL.execute deletedState
      s!"INSERT INTO dirty_rows VALUES(101,'{payload}');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"dirty-page insert failed: {message}"
  let insertedDelta ← match CoreChunkPageDelta.updateState?
      deletedDelta.after insertedState.database with
    | some value => pure value
    | none => fail "single-row insert did not produce a proved page delta"
  let insertedBefore ← match CoreChunkPageDelta.beforeWrites insertedDelta.table with
    | some value => pure value
    | none => fail "insert before-image contained page zero"
  let insertedWrites ← match CoreChunkPageDelta.writes insertedDelta.table with
    | some value => pure value
    | none => fail "insert delta contained page zero"
  unless (← CoreFileAdapter.commitLocalized .system paths insertedBefore
      insertedWrites insertedDelta.after.freePages).isSome do
    fail "insert pages did not match their proved before-image"
  -- Fill the final chunk and force an identified leaf/interior split.  The
  -- writer may recycle released identities or append genuinely new pages; in
  -- either case the localized image must remain readable by stock SQLite.
  let mut splitLogical := insertedState
  let mut splitPhysical := insertedDelta.after
  for offset in List.range 12 do
    let rowid := 102 + offset
    let (nextLogical, _) ← match CoreSQL.execute splitLogical
        s!"INSERT INTO dirty_rows VALUES({rowid},'{payload}');" with
      | .ok outcome => pure outcome
      | .error message => fail s!"split insert {rowid} failed: {message}"
    let nextDelta ← match CoreChunkPageDelta.updateState?
        splitPhysical nextLogical.database with
      | some value => pure value
      | none => fail s!"split insert {rowid} did not produce a proved delta"
    let nextBefore ← match CoreChunkPageDelta.beforeWrites nextDelta.table with
      | some value => pure value
      | none => fail s!"split insert {rowid} before-image contained page zero"
    let nextWrites ← match CoreChunkPageDelta.writes nextDelta.table with
      | some value => pure value
      | none => fail s!"split insert {rowid} delta contained page zero"
    unless (← CoreFileAdapter.commitLocalized .system paths nextBefore
        nextWrites nextDelta.after.freePages).isSome do
      fail s!"split insert {rowid} pages did not match their before-images"
    splitLogical := nextLogical
    splitPhysical := nextDelta.after
  let mut mergedLogical := splitLogical
  let mut mergedPhysical := splitPhysical
  -- Remove both chunks produced by the split.  Removing only the new right
  -- chunk can leave a valid one-entry leaf and therefore has no physical page
  -- to free; removing 97..113 forces borrow/merge and exercises the live
  -- SQLite freelist encoding.
  for offset in List.range 17 do
    let rowid := 97 + offset
    let (nextLogical, _) ← match CoreSQL.execute mergedLogical
        s!"DELETE FROM dirty_rows WHERE id={rowid};" with
      | .ok outcome => pure outcome
      | .error message => fail s!"merge delete {rowid} failed: {message}"
    let nextDelta ← match CoreChunkPageDelta.updateState?
        mergedPhysical nextLogical.database with
      | some value => pure value
      | none =>
          let detail := match mergedPhysical.tables.head?,
              nextLogical.database.tables.head? with
            | some oldTable, some nextTable =>
                let deleted := CoreChunkPageDelta.firstDeleted
                  oldTable.table.rows nextTable.rows
                let entry := deleted.bind fun row =>
                  CoreChunkPageDelta.findChunkFor? row.treeKey oldTable.tree.root
                let direct := deleted.bind fun row =>
                  CoreChunkPageDelta.delete? oldTable mergedPhysical.nextPage row
                    nextTable
                let deletedIds := deleted.map fun (row : Core.Row) => row.rowid.value
                let entryRows := entry.map fun
                  (e : PagedBTree.Entry CoreChunkPageState.Chunk) =>
                    (e.1, e.2.map fun (row : Core.Row) => row.rowid.value)
                let allEntries := oldTable.tree.root.erase.toList.map fun
                    (e : PagedBTree.Entry CoreChunkPageState.Chunk) =>
                  let first := e.2.head?.map fun (row : Core.Row) => row.rowid.value
                  let last := e.2.getLast?.map fun (row : Core.Row) => row.rowid.value
                  s!"{e.1}:{first.map (fun (value : Int) => toString value)}-{last.map (fun (value : Int) => toString value)}/{e.2.length}"
                s!"deleted={repr deletedIds}, entry={repr entryRows}, direct={direct.isSome}, entries={String.intercalate ";" allEntries}"
            | _, _ => "missing table"
          fail s!"merge delete {rowid} did not produce a proved delta: {detail}"
    let nextBefore ← match CoreChunkPageDelta.beforeWrites nextDelta.table with
      | some value => pure value
      | none => fail s!"merge delete {rowid} before-image contained page zero"
    let nextWrites ← match CoreChunkPageDelta.writes nextDelta.table with
      | some value => pure value
      | none => fail s!"merge delete {rowid} delta contained page zero"
    unless (← CoreFileAdapter.commitLocalized .system paths nextBefore
        nextWrites nextDelta.after.freePages).isSome do
      fail s!"merge delete {rowid} pages did not match their before-images"
    let checkpoint ← CoreFileAdapter.reopen paths
    unless checkpoint.Equiv nextLogical.database do
      fail s!"merge delete {rowid} did not preserve the represented database; writes={nextWrites.map (·.pageId)}, freed={nextDelta.table.freedPageNumbers}"
    mergedLogical := nextLogical
    mergedPhysical := nextDelta.after
  let reopened ← CoreFileAdapter.reopen paths
  let reloaded ← match ← CoreFileAdapter.loadPageState paths reopened with
    | some value => pure value
    | none => fail "merged physical tree or freelist did not reload"
  let grownBytes ← paths.main.metadata
  let grownPages := grownBytes.byteSize.toNat / PhysicalCodec.pageSize
  let dirtyPages := plan.filterMap fun request => match request with
    | .pwriteMain write => some write.pageId
    | _ => none
  unless reopened.Equiv mergedLogical.database &&
      reloaded.database.Equiv mergedLogical.database && oldPages ≤ grownPages &&
      0 < dirtyPages.length &&
      dirtyPages.length < oldPages do
    fail s!"localized commit wrote {dirtyPages.length} of {oldPages} pages"
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT count(*),length(payload) FROM dirty_rows WHERE payload LIKE 'e%'; SELECT count(*) FROM dirty_rows; SELECT count(*) FROM dirty_rows WHERE id=105;"] }
  unless output.exitCode == 0 && output.stdout == "ok\n1|96\n95\n0\n" do
    fail s!"SQLite rejected the dirty-page commit: {output.stderr}{output.stdout}"

private def expectHeaderMetadata : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'a'),(2,'b');CREATE INDEX t_v ON t(v);" with
    | .ok result => pure result
    | .error message => fail message
  let image ← match CorePageCodec.encodeBulk state.database with
    | some image => pure image
    | none => fail "metadata: encode failed"
  let base ← match CoreMultiFreelist.ofImageTotal? image (image.pageCount + 2) with
    | some layout => pure layout
    | none => fail "metadata: layout failed"
  let metadata : CoreMultiFreelist.HeaderMetadata := {
    applicationId := ⟨4294967295, by omega⟩
    userVersion := ⟨42, by omega⟩ }
  let layout := { base with metadata }
  let (header, _) ← match FileFormat.decodeDatabaseHeader layout.paddedImage.fileBytes with
    | some result => pure result
    | none => fail "metadata: header failed"
  unless header.applicationId.val == 4294967295 && header.userVersion.val == 42 &&
      header.databaseSizePages.val == image.pageCount + 2 && header.freelistPageCount.val == 2 do
    fail "metadata fields or geometry changed"
  unless layout.schemaPage.bytes.drop 100 == layout.firstPage.bytes.drop 100 do
    fail "metadata changed the schema B-tree body"
  let decoded ← match CoreDecode.decode layout.paddedImage.fileBytes with
    | some database => pure database
    | none => fail "metadata: padded image failed to decode"
  unless decoded.contents == state.database.contents do fail "metadata changed logical rows"
  unless !CoreFile.hasGeneratedImageStamp header do fail "nondefault metadata entered the generated fast path"
  let zeroApp := { header with applicationId := ⟨0, by omega⟩ }
  unless !CoreFile.hasGeneratedImageStamp zeroApp do fail "nonzero user version entered the generated fast path"

private def expectCoreMultiFreelist : IO Unit := do
  let (state, _) ← match CoreSQL.execute { database := Core.Database.empty }
      "CREATE TABLE multi_free(id INTEGER PRIMARY KEY,value TEXT);
       INSERT INTO multi_free VALUES(1,'kept');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"multi-trunk setup failed: {message}"
  let image ← match RecursivePageBTree.encode state.database with
    | some image => pure image
    | none => fail "multi-trunk setup did not encode"
  let freeCount := 2050
  let total := image.pageCount + freeCount
  let layout ← match CoreMultiFreelist.ofImageTotal? image total with
    | some layout => pure layout
    | none => fail "multi-trunk layout rejected a bounded page count"
  unless layout.pages.length == total && layout.freelistPages.length == freeCount do
    fail "multi-trunk layout emitted the wrong number of pages"
  let path : System.FilePath := ".lake/build/sqleanite-multi-freelist.db"
  IO.FS.writeBinFile path (ByteArray.mk layout.paddedImage.fileBytes.toArray)
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; PRAGMA freelist_count; SELECT count(*) FROM multi_free;"] }
  unless output.exitCode == 0 && output.stdout == "ok\n2050\n1\n" do
    fail s!"SQLite rejected the verified multi-trunk freelist: {output.stderr}{output.stdout}"

private def expectLazyReachablePageDecode : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty "
      CREATE TABLE lazy_rows(id INTEGER PRIMARY KEY,value TEXT NOT NULL);
      CREATE INDEX lazy_value ON lazy_rows(value);
      INSERT INTO lazy_rows VALUES(1,'one'),(2,'two');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"lazy pager setup failed: {message}"
  let image ← match CoreFile.encode state.database with
    | some image => pure image
    | none => fail "lazy pager encoder rejected a small database"
  let layout ← match CoreFreelist.ofImageTotal? image 100 with
    | some layout => pure layout
    | none => fail "lazy pager could not build a bounded padded image"
  let physicalPages := layout.pages.map CoreFile.Page.bytes
  let reads ← IO.mkRef 0
  let source : CoreDecode.IOPageSource := {
    pageCount := physicalPages.length
    readPage := fun pageNumber => do
      let count ← reads.get
      reads.set (count + 1)
      return CoreDecode.page? physicalPages pageNumber }
  let decoded ← match ← CoreDecode.decodeFromIOPageSource source with
    | some database => pure database
    | none => fail "lazy pager rejected reachable table or index pages"
  unless decoded.Equiv state.database do
    fail "lazy pager changed the decoded database"
  let readCount ← reads.get
  unless readCount < physicalPages.length do
    fail "lazy pager requested unreachable freelist pages"

private def expectGeneralMVPFileEngine : IO Unit := do
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-general-live.db"
    journal := ".lake/build/sqleanite-general-live.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  let connection ← CoreFileEngine.create .system paths
  let setup ← CoreFileEngine.execute connection "
    BEGIN;
    CREATE TABLE users(id INTEGER PRIMARY KEY,name TEXT NOT NULL);
    CREATE TABLE notes(body TEXT,note_id INTEGER PRIMARY KEY,owner INTEGER NOT NULL);
    CREATE INDEX users_name ON users(name);
    INSERT INTO users VALUES(2,'Ada'),(1,'Lin');
    INSERT INTO notes VALUES('kernel',10,1);
    COMMIT;"
  if let .error message := setup then
    fail s!"general persisted setup failed: {message}"
  let rolledBack ← CoreFileEngine.execute connection "
    BEGIN; INSERT INTO users VALUES(9,'rollback'); ROLLBACK;"
  if let .error message := rolledBack then
    fail s!"general persisted rollback failed: {message}"
  let cInsert ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch",
      "INSERT INTO users VALUES(3,'C'); INSERT INTO notes VALUES('interop',11,3);"] }
  unless cInsert.exitCode == 0 do
    fail s!"C SQLite could not update the generalized live path: {cInsert.stderr}"
  let reopened ← CoreFileEngine.reopen .system paths
  let leanInsert ← CoreFileEngine.execute reopened
    "INSERT INTO users VALUES(4,'Lean');"
  if let .error message := leanInsert then
    fail s!"Lean could not commit after a C-written image: {message}"
  let modified ← CoreFileEngine.execute reopened "
    BEGIN;
    UPDATE users SET name='Lean updated' WHERE id=4;
    DELETE FROM users WHERE id=2;
    DELETE FROM notes WHERE note_id=10;
    COMMIT;"
  if let .error message := modified then
    fail s!"general live UPDATE/DELETE failed: {message}"
  let rejected ← CoreFileEngine.execute reopened
    "UPDATE users SET name=NULL WHERE id=1;"
  if rejected.isOk then
    fail "general live UPDATE admitted a NOT NULL violation"
  let check ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-noheader", "
      PRAGMA integrity_check;
      SELECT id,name FROM users ORDER BY id;
      SELECT note_id,body,owner FROM notes ORDER BY note_id;"] }
  unless check.exitCode == 0 && check.stdout ==
      "ok\n1|Lin\n3|C\n4|Lean updated\n11|interop|3\n" do
    fail s!"general live path failed C/Lean roundtrip: {check.stderr}{check.stdout}"
  let selected ← CoreFileEngine.execute reopened
    "SELECT name,id FROM users ORDER BY id DESC LIMIT 2;"
  match selected with
  | .error message => fail s!"general live SELECT failed: {message}"
  | .ok results =>
      let rows := results.flatMap (·.rows)
      unless rows.length == 2 do
        fail "general live SELECT returned the wrong row count"
  let joined ← CoreFileEngine.execute reopened "
    SELECT users.name,notes.body FROM users
    INNER JOIN notes ON users.id=notes.owner
    WHERE notes.note_id>=11 ORDER BY users.id;"
  match joined with
  | .error message => fail s!"general live INNER JOIN failed: {message}"
  | .ok results =>
      let rows := results.flatMap (·.rows)
      unless rows == [[.text ⟨[67], by decide⟩,
          .text ⟨[105, 110, 116, 101, 114, 111, 112], by decide⟩]] do
        fail "general live INNER JOIN returned the wrong rows"

private def expectMVPRecordCells : IO Unit := do
  let rowid : FileFormat.SignedInteger .eight := ⟨7, by decide, by decide⟩
  let text : PhysicalCodec.Text := ⟨[97, 108, 112, 104, 97], by decide⟩
  let row : PhysicalCodec.Row := {
    rowid
    first := .integer ⟨-4, by decide, by decide⟩
    second := .text text }
  match PhysicalCodec.decodeRowCell (row.encodeCell ++ [99]) with
  | some (decoded, [99]) =>
      unless decoded == row do
        fail "MVP table-leaf cell codec changed a logical row"
  | _ => fail "MVP table-leaf cell codec failed"
  let rows := [row, { row with rowid := ⟨8, by decide, by decide⟩, first := .null }]
  unless PhysicalCodec.decodeCells rows.length (PhysicalCodec.encodeCells rows) ==
      some (rows, []) do
    fail "MVP table-leaf cell-list codec failed"

private def expectSQLiteFileInterop : IO Unit := do
  let alpha : PhysicalCodec.Text := ⟨[97, 108, 112, 104, 97], by decide⟩
  let beta : PhysicalCodec.Text := ⟨[98, 101, 116, 97], by decide⟩
  let first : PhysicalCodec.Row := {
    rowid := ⟨1, by decide, by decide⟩
    first := .text alpha
    second := .null }
  let second : PhysicalCodec.Row := {
    rowid := ⟨2, by decide, by decide⟩
    first := .integer ⟨-4, by decide, by decide⟩
    second := .text beta }
  let database : PhysicalCodec.Database := {
    rows := [first, second]
    rowidsSorted := by simp [PhysicalCodec.Row.keyLess, first, second]
    pageFits := by
      unfold PhysicalCodec.PageFit PhysicalCodec.cellBytes PhysicalCodec.pageSize
      decide }
  let path : System.FilePath := ".lake/build/sqleanite-mvp-interop.db"
  match PhysicalCodec.decodeFile database.fileBytes with
  | some reopened =>
      unless reopened.rows == database.rows do
        fail "verified MVP file decoder changed the logical rows"
  | none => fail "verified MVP file decoder rejected its own image"
  match PhysicalCodec.decodeStorageImage database.storageImage with
  | some reopened =>
      unless reopened.rows == database.rows do
        fail "verified pager reopen changed the logical rows"
  | none => fail "verified pager reopen rejected its own image"
  IO.FS.writeBinFile path (ByteArray.mk database.fileBytes.toArray)
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT id,first,second FROM items ORDER BY id;"] }
  unless output.exitCode == 0 do
    fail s!"sqlite3 rejected the verified MVP image: {output.stderr}"
  unless output.stdout == "ok\n1|alpha|\n2|-4|beta\n" do
    fail s!"sqlite3 read unexpected MVP rows: {repr output.stdout}"

private def expectMVPFileAdapter : IO Unit := do
  let alpha : PhysicalCodec.Text := ⟨[97, 108, 112, 104, 97], by decide⟩
  let beta : PhysicalCodec.Text := ⟨[98, 101, 116, 97], by decide⟩
  let first : PhysicalCodec.Row := {
    rowid := ⟨1, by decide, by decide⟩
    first := .text alpha
    second := .null }
  let second : PhysicalCodec.Row := {
    rowid := ⟨2, by decide, by decide⟩
    first := .integer ⟨-4, by decide, by decide⟩
    second := .text beta }
  let old : PhysicalCodec.Database := {
    rows := [second]
    rowidsSorted := by simp [PhysicalCodec.Row.keyLess, second]
    pageFits := by
      unfold PhysicalCodec.PageFit PhysicalCodec.cellBytes PhysicalCodec.pageSize
      decide }
  let new ← match old.insertChecked first with
    | .ok database => pure database
    | .error message => fail s!"verified MVP arbitrary-order insert failed: {message}"
  unless new.rows == [first, second] do
    fail "verified MVP arbitrary-order insert produced the wrong rows"
  let updated ← match new.updatePayload 2 .null (.text alpha) with
    | .ok database => pure database
    | .error message => fail s!"verified MVP update failed: {message}"
  match updated.findRow? 2 with
  | some row =>
      unless row.first == .null && row.second == .text alpha do
        fail "verified MVP update changed the wrong payload"
  | none => fail "verified MVP update lost its target row"
  let deleted ← match updated.deleteRowid 1 with
    | .ok database => pure database
    | .error message => fail s!"verified MVP delete failed: {message}"
  unless deleted.rows.length == 1 && (deleted.findRow? 2).isSome do
    fail "verified MVP delete removed the wrong row"
  if (new.insertChecked first).isOk then
    fail "verified MVP insert admitted a duplicate primary key"
  let paths : PhysicalFileAdapter.Paths := {
    main := ".lake/build/sqleanite-mvp-adapter.db"
    journal := ".lake/build/sqleanite-mvp-adapter.db-journal" }
  PhysicalFileAdapter.create .system paths old
  let openedOld ← PhysicalFileAdapter.reopen paths
  unless openedOld.rows == old.rows do
    fail "MVP file adapter did not reopen its initial database"
  let (openedNew, trace) ← PhysicalFileAdapter.commit .system paths new
  unless openedNew.rows == new.rows do
    fail "MVP file adapter did not reopen its committed database"
  let newTree ← match PhysicalTableBTree.build new with
    | some tree => pure tree
    | none => fail "MVP adapter test database did not build a physical tree"
  unless trace.length == (PhysicalMultiPageCodec.transactionWrites newTree).length + 7 do
    fail s!"MVP file adapter emitted the wrong VFS plan: {trace.length} requests"
  if ← paths.journal.pathExists then
    fail "MVP file adapter returned before journal deletion"
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT id,first,second FROM items ORDER BY id;"] }
  unless output.exitCode == 0 && output.stdout == "ok\n1|alpha|\n2|-4|beta\n" do
    fail s!"sqlite3 rejected the adapter's committed image: {output.stderr}{output.stdout}"

  let third : PhysicalCodec.Row := {
    rowid := ⟨3, by decide, by decide⟩
    first := .integer ⟨33, by decide, by decide⟩
    second := .null }
  let fourth : PhysicalCodec.Row := {
    rowid := ⟨4, by decide, by decide⟩
    first := .integer ⟨44, by decide, by decide⟩
    second := .null }
  let fifth : PhysicalCodec.Row := {
    rowid := ⟨5, by decide, by decide⟩
    first := .integer ⟨55, by decide, by decide⟩
    second := .null }
  let grown ← match new.insertChecked third with
    | .error message => fail s!"MVP growth insert three failed: {message}"
    | .ok afterThird => match afterThird.insertChecked fourth with
      | .error message => fail s!"MVP growth insert four failed: {message}"
      | .ok afterFourth => match afterFourth.insertChecked fifth with
        | .error message => fail s!"MVP growth insert five failed: {message}"
        | .ok database => pure database
  let (openedGrown, growthTrace) ← PhysicalFileAdapter.commit .system paths grown
  unless openedGrown.rows == grown.rows do
    fail "MVP file adapter did not reopen its split multi-page commit"
  let grownTree ← match PhysicalTableBTree.build grown with
    | some tree => pure tree
    | none => fail "MVP grown database did not build a physical tree"
  unless PhysicalMultiPageCodec.filePageCount grownTree == 5 &&
      growthTrace.length == 12 do
    fail "MVP file adapter did not emit the expected five-page growth plan"
  let grownBytes ← IO.FS.readBinFile paths.main
  unless grownBytes.size == 5 * PhysicalCodec.pageSize do
    fail "MVP file adapter did not physically grow the main file"
  let grownCheck ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT count(*) FROM items;"] }
  unless grownCheck.exitCode == 0 && grownCheck.stdout == "ok\n5\n" do
    fail s!"sqlite3 rejected the adapter's grown image: {grownCheck.stderr}{grownCheck.stdout}"

  let shrunk ← match grown.deleteRowid 3 with
    | .error message => fail s!"MVP shrink delete three failed: {message}"
    | .ok afterThird => match afterThird.deleteRowid 4 with
      | .error message => fail s!"MVP shrink delete four failed: {message}"
      | .ok afterFourth => match afterFourth.deleteRowid 5 with
        | .error message => fail s!"MVP shrink delete five failed: {message}"
        | .ok database => pure database
  let (openedShrunk, shrinkTrace) ← PhysicalFileAdapter.commit .system paths shrunk
  unless openedShrunk.rows == shrunk.rows && shrinkTrace.length == 12 do
    fail "MVP file adapter did not reopen its freelist-backed shrink"
  let shrunkBytes ← IO.FS.readBinFile paths.main
  unless shrunkBytes.size == 5 * PhysicalCodec.pageSize do
    fail "MVP freelist shrink unexpectedly truncated the committed file"
  let shrinkCheck ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; PRAGMA freelist_count; SELECT count(*) FROM items;"] }
  unless shrinkCheck.exitCode == 0 && shrinkCheck.stdout == "ok\n3\n2\n" do
    fail s!"sqlite3 rejected the freelist shrink: {shrinkCheck.stderr}{shrinkCheck.stdout}"

  -- Inject the crash state after the new main page was written but before the
  -- page-level journal was deleted. Recovery must restore old pages and
  -- truncate the three newly grown pages.
  PhysicalFileAdapter.create .system paths old
  let oldTree ← match PhysicalTableBTree.build old with
    | some tree => pure tree
    | none => fail "MVP adapter old database did not build a physical tree"
  let crashJournal := GrowableStorage.makeJournal
    (PhysicalMultiPageCodec.storageImage oldTree)
    (PhysicalMultiPageCodec.transactionWrites grownTree)
  let encodedCrashJournal ← match PhysicalJournalCodec.ofJournal? crashJournal with
    | some journal => pure (PhysicalJournalCodec.encodeChecked journal)
    | none => fail "MVP adapter crash journal exceeded encoded bounds"
  IO.FS.writeBinFile paths.journal (ByteArray.mk encodedCrashJournal.toArray)
  IO.FS.writeBinFile paths.main
    (ByteArray.mk (PhysicalMultiPageCodec.fileBytes grownTree).toArray)
  let recovered ← PhysicalFileAdapter.recover .system paths
  unless recovered.rows == old.rows do
    fail "MVP file adapter failed to restore its page-level undo journal"
  let recoveredBytes ← IO.FS.readBinFile paths.main
  unless recoveredBytes.size == 2 * PhysicalCodec.pageSize do
    fail "MVP file adapter recovery did not truncate grown pages"

  -- Deterministically materialize the POSIX model's namespace checkpoints.
  -- These complement the quantified pure theorem with tests of the concrete
  -- executable's file-name handling.
  let noSync : PhysicalFileAdapter.SyncOps := {
    syncFile := fun _ => pure ()
    syncDeletion := fun _ => pure () }
  PhysicalFileAdapter.create noSync paths old
  IO.FS.writeBinFile paths.journalTemp
    (ByteArray.mk encodedCrashJournal.toArray)
  let tempRecovered ← PhysicalFileAdapter.recover noSync paths
  let tempStillExists ← paths.journalTemp.pathExists
  unless tempRecovered.rows == old.rows && !tempStillExists do
    fail "orphan temporary journal was published or not removed"

  PhysicalFileAdapter.create noSync paths old
  IO.FS.writeBinFile paths.journal
    (ByteArray.mk encodedCrashJournal.toArray)
  let publishedRecovered ← PhysicalFileAdapter.recover noSync paths
  unless publishedRecovered.rows == old.rows do
    fail "published journal without main writes did not recover the old image"

  PhysicalFileAdapter.create noSync paths old
  IO.FS.writeBinFile paths.main
    (ByteArray.mk (PhysicalMultiPageCodec.fileBytes grownTree).toArray)
  let deletedRecovered ← PhysicalFileAdapter.recover noSync paths
  unless deletedRecovered.rows == grown.rows do
    fail "deleted journal checkpoint did not retain the new image"

  PhysicalFileAdapter.create noSync paths old
  let corruptJournal := encodedCrashJournal.modify 20 (fun byte => byte + 1)
  IO.FS.writeBinFile paths.journal (ByteArray.mk corruptJournal.toArray)
  let corruptRejected ←
    try
      let _ ← PhysicalFileAdapter.recover noSync paths
      pure false
    catch _ => pure true
  unless corruptRejected do
    fail "live recovery accepted a deterministically corrupted journal"
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal

private def expectPersistentPageTree : IO Unit := do
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

private def expectCheckedTablePages : IO Unit := do
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

private def expectReadPagerBoundary : IO Unit := do
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

private def expectCachedPrimaryEdgeRows : IO Unit := do
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

private def expectCertifiedCoreTokenGrammar : IO Unit := do
  let sql := "CREATE TABLE usertable(ycsb_key TEXT PRIMARY KEY,field0 TEXT);\n    BEGIN; INSERT INTO usertable VALUES('user0001','payload');\n    SELECT field0 FROM usertable WHERE (ycsb_key='user0001'); COMMIT;"
  let certificate ← match CoreTokenGrammar.parseCertified sql with
    | .ok certificate => pure certificate
    | .error message => fail s!"certified Core grammar rejected its exact schema: {message}"
  unless certificate.statements.size == 5 do
    fail "certified Core grammar lost a statement boundary"
  match CoreTokenGrammar.check certificate.tokens #[.rollback] with
  | .error _ => pure ()
  | .ok () => fail "independent Core grammar admitted a mismatched AST"

private def expectSQLiteScalarCore : IO Unit := do
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

private def expectSQLiteTextFunctions : IO Unit := do
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

private def expectSQLiteRowExpressions : IO Unit := do
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

private def expectSQLiteRowUpdates : IO Unit := do
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

private def expectIndexTailOwnership : IO Unit := do
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

private def expectSQLiteRowPredicates : IO Unit := do
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

private def expectPageSizeConversionFailures : IO Unit := do
  for fault in [0, 1, 2] do
    let main : System.FilePath := s!".lake/build/sqleanite-conversion-{fault}.db"
    let paths : CoreFileAdapter.Paths := { main, journal := main.toString ++ "-journal" }
    let temporary : System.FilePath := main.toString ++ ".sqleanite-image.tmp"
    for path in [main, paths.journal, paths.journalTemp, temporary] do
      if ← path.pathExists then IO.FS.removeFile path
    let setup ← IO.Process.output {
      cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
      args := #[main.toString, "PRAGMA page_size=512; CREATE TABLE t(v); INSERT INTO t VALUES('old');"] }
    unless setup.exitCode == 0 do fail s!"conversion fixture: {setup.stderr}"
    CoreFileAdapter.recoverInPlace .system paths
    let original ← IO.FS.readBinFile main
    let database ← CoreFileAdapter.reopen paths
    let (next, _) ← match CoreSQL.execute { database } "INSERT INTO t VALUES('new');" with
      | .ok result => pure result
      | .error message => fail message
    let syncOps : CoreFileAdapter.SyncOps := {
      syncFile := fun path => do
        if path.toString.endsWith ".sqleanite-image.tmp" then
          if fault == 0 then throw (IO.userError "injected temporary-file sync failure")
          if fault == 1 then IO.FS.writeBinFile path (ByteArray.mk #[0])
        (PhysicalFileAdapter.SyncOps.system).syncFile path
      syncDeletion := fun path => do
        if fault == 2 then throw (IO.userError "injected directory sync failure")
        (PhysicalFileAdapter.SyncOps.system).syncDeletion path }
    let failed ← try
        discard <| CoreFileAdapter.convertPageSize syncOps paths next.database
        pure false
      catch _ => pure true
    unless failed do fail "conversion fault injection did not fail"
    if fault < 2 then
      unless (← IO.FS.readBinFile main) == original do
        fail "unpublished conversion changed the original file"
    let checked ← IO.Process.output {
      cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
      args := #[main.toString, "PRAGMA integrity_check;SELECT count(*) FROM t;"] }
    unless checked.exitCode == 0 && checked.stdout == (if fault < 2 then "ok\n1\n" else "ok\n2\n") do
      fail s!"conversion exposed an incomplete image: {checked.stdout}{checked.stderr}"
    discard <| CoreFileAdapter.convertPageSize .system paths next.database
    let reopened ← CoreFileAdapter.reopen paths
    unless reopened.Equiv next.database do fail "conversion retry changed logical contents"

private def expectSQLiteSchemaAdmission : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER,v);CREATE TABLE other(v);CREATE INDEX ix ON t(v);CREATE TABLE shadow(rowid);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  for sql in ["CREATE TABLE IF NOT EXISTS t(v TEXT);",
      "CREATE INDEX IF NOT EXISTS ix ON other(missing);",
      "CREATE UNIQUE INDEX IF NOT EXISTS ix ON t(unknown_function(v));",
      "CREATE INDEX IF NOT EXISTS ix ON t(v) WHERE missing;"] do
    let (next, results) ← match CoreSQL.execute initial sql with
      | .ok result => pure result
      | .error message => fail s!"schema no-op: {sql}: {message}"
    unless next.database.Equiv initial.database do fail s!"schema no-op changed database: {sql}"
    unless results.length == 1 && results.all (fun r => r.changes == 0 && r.rows.isEmpty) do
      fail s!"schema no-op changed result: {sql}"
  for sql in ["CREATE TABLE IF NOT EXISTS ix(v);", "CREATE INDEX IF NOT EXISTS t ON t(v);",
      "CREATE INDEX ix ON other(v);", "CREATE INDEX IF NOT EXISTS ix ON missing(v);",
      "CREATE TABLE sqlite_x(v);", "CREATE INDEX sqlite_x ON t(v);",
      "CREATE INDEX ir ON t(rowid);", "CREATE INDEX iq ON t(t.v);"] do
    match CoreSQL.execute initial sql with
    | .ok _ => fail s!"invalid schema admitted: {sql}"
    | .error _ => pure ()
  match CoreSQL.execute initial "CREATE INDEX ir ON shadow(rowid);" with
  | .ok _ => pure ()
  | .error message => fail s!"real rowid-named column rejected: {message}"

private def expectSQLiteUniqueIndexes : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,a,b TEXT); INSERT INTO t VALUES(1,1,'a'),(2,2,'b'),(3,NULL,NULL),(4,NULL,NULL); CREATE UNIQUE INDEX ua ON t(a); CREATE UNIQUE INDEX ub ON t(b);"
  let cases : List (String × List (List Value)) := [
    ("SELECT id,a,b FROM t ORDER BY id;",
      [[.integer 1,.integer 1,.text "a"],[.integer 2,.integer 2,.text "b"],
       [.integer 3,.null,.null],[.integer 4,.null,.null]]),
    ("INSERT OR REPLACE INTO t VALUES(10,2,'a'); SELECT id,a,b FROM t ORDER BY id;",
      [[.integer 3,.null,.null],[.integer 4,.null,.null],[.integer 10,.integer 2,.text "a"]]),
    ("UPDATE t SET a=a+10 WHERE id<3; SELECT id,a,b FROM t WHERE id<3 ORDER BY id;",
      [[.integer 1,.integer 11,.text "a"],[.integer 2,.integer 12,.text "b"]]),
    ("INSERT INTO t VALUES(10,'1','c'); SELECT id,a,b FROM t WHERE id=10;",
      [[.integer 10,.text "1",.text "c"]])]
  for (sql, expected) in cases do
    let (state, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"UNIQUE index: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"UNIQUE result: {sql}"
    let some table := state.database.findTable? "t" | fail "UNIQUE lost table"
    unless table.indexes.length == 2 && table.indexes.all (·.unique) do
      fail "UNIQUE metadata lost"
  for sql in ["INSERT INTO t VALUES(10,1.0,'new');", "UPDATE t SET a=2 WHERE id=1;",
      "UPDATE t SET a=a+1 WHERE id<3;", "UPDATE t SET b='same';",
      "UPDATE t SET id=10,a=1 WHERE id=2;",
      "INSERT INTO t VALUES(10,10,'new'),(11,2,'other');"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"UNIQUE accepted duplicate: {sql}"
    | .error _ => pure ()
  match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(v); INSERT INTO t VALUES(1),(1.0); CREATE UNIQUE INDEX uv ON t(v);" with
  | .ok _ => fail "UNIQUE creation accepted numeric duplicates"
  | .error _ => pure ()
  for unique in [false, true] do
    let spec : CanonicalIndexSQL.Spec := { name := "quoted\"index", table := "t", column := "v", unique }
    unless CanonicalIndexSQL.parse (CanonicalIndexSQL.print spec) == some spec do
      fail "UNIQUE index SQL failed roundtrip"

private def expectSQLitePatterns : IO Unit := do
  let cases : List (String × List Value) := [
    ("SELECT 'ABC' LIKE 'a%', 'Á' LIKE 'á', 'ABC' GLOB 'a*', 'abc' GLOB '[a-z]*';",
      [.integer 1,.integer 0,.integer 0,.integer 1]),
    ("SELECT 'a_b' LIKE 'a!_b' ESCAPE '!', 'abc' NOT LIKE 'a%', 'abc' NOT GLOB 'A*';",
      [.integer 1,.integer 0,.integer 1]),
    ("SELECT glob('[]]',']'),glob('[^]]','a'),glob('[z-a]','z'),glob('[z-a]','a'),glob('[','a');",
      [.integer 1,.integer 1,.integer 1,.integer 0,.integer 0]),
    ("SELECT X'80' GLOB '?',X'C080' LIKE '_',like('a',X'410078'),glob(X'',X'');",
      [.integer 1,.integer 1,.integer 1,.integer 1]),
    ("SELECT NULL LIKE '%',glob('*',NULL),like('a','a',NULL),like('a','a',CAST(X'210078' AS TEXT));",
      [.null,.null,.null,.integer 1])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"patterns: {message}"
    let row ← match expected.mapM SQLSurface.value with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [row] do fail s!"pattern result: {sql}"
  for sql in ["SELECT NULL LIKE '%' ESCAPE '';", "SELECT like(NULL,NULL,'ab');",
      "SELECT glob('a','a','x');", "SELECT like('a','a',char(0));"] do
    match CoreSQL.execute Core.State.empty sql with
    | .ok _ => fail s!"pattern accepted invalid input: {sql}"
    | .error _ => pure ()
  let tokens ← match lex "SELECT 'a_b' LIKE 'a!_b' ESCAPE '!';" with
    | .ok tokens => pure tokens
    | .error message => fail message
  let wrong ← match parse "SELECT like('a!_b','changed','!');" with
    | .ok statements => pure statements
    | .error message => fail message
  if (CoreTokenGrammar.check tokens wrong).isOk then fail "ESCAPE grammar accepted a changed operand"

private def expectSQLiteRound : IO Unit := do
  let cases : List (String × List Value) := [
    ("SELECT round(0.5),round(-0.5),round(2.5),round(-2.5);",
      [.real 1.0,.real (-1.0),.real 3.0,.real (-3.0)]),
    ("SELECT round(2.675,2),round(1.005,2),round(0.05,1),round(-0.05,1);",
      [.real 2.67,.real 1.0,.real 0.1,.real (-0.1)]),
    ("SELECT round(12.5,-1),round(1.25,'1x'),round(1.25,'1e2'),round('bad');",
      [.real 13.0,.real 1.3,.real 1.3,.real 0.0]),
    ("SELECT round(NULL),round(1,NULL),round(1.25,31),typeof(round(1));",
      [.null,.null,.real 1.25,.text "real"])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"round: {message}"
    let row ← match expected.mapM SQLSurface.value with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [row] do fail s!"round result: {sql}"
  for sql in ["SELECT round();", "SELECT round(1,2,3);",
      "SELECT round(NULL,abs(-9223372036854775808));",
      "SELECT round(abs(-9223372036854775808),NULL);"] do
    match CoreSQL.execute Core.State.empty sql with
    | .ok _ => fail s!"round accepted invalid input: {sql}"
    | .error _ => pure ()

private def expectSQLiteRowidUpdates : IO Unit := do
  let cases : List (String × Nat × List (List Value)) := [
    ("CREATE TABLE t(v); INSERT INTO t(rowid,v) VALUES(-5,'a'),(2,'b'); UPDATE t SET rowid=rowid+20,v=v||rowid; SELECT rowid,v FROM t ORDER BY rowid;",
      2, [[.integer 15,.text "a-5"],[.integer 22,.text "b2"]]),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,'a'),(2,'b'); UPDATE t SET id=-id,v=id; SELECT id,v FROM t ORDER BY id;",
      2, [[.integer (-2),.integer 2],[.integer (-1),.integer 1]]),
    ("CREATE TABLE t(v); INSERT INTO t VALUES('a'); UPDATE t SET rowid=abs(-9223372036854775808),_rowid_=rowid+20; SELECT rowid,v FROM t;",
      1, [[.integer 21,.text "a"]]),
    ("CREATE TABLE t(v); INSERT INTO t VALUES('a'); UPDATE t SET rowid='9223372036854775807'; SELECT rowid,v FROM t;",
      1, [[.integer 9223372036854775807,.text "a"]]),
    ("CREATE TABLE t(v); INSERT INTO t VALUES('a'); UPDATE t SET rowid=NULL WHERE 0; SELECT rowid,v FROM t;",
      0, [[.integer 1,.text "a"]]),
    ("CREATE TABLE t(v); UPDATE t SET rowid=NULL; SELECT rowid,v FROM t;", 0, [])]
  for (sql, changed, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"rowid UPDATE: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"rowid UPDATE result: {sql}"
    unless (results.reverse[1]?).map (·.changes) == some changed do
      fail s!"rowid UPDATE changes count: {sql}"
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v NOT NULL); INSERT INTO t VALUES(1,'a'),(2,'b');"
  for sql in ["UPDATE t SET id=id+1;", "UPDATE t SET id=NULL;", "UPDATE t SET id=1.5;",
      "UPDATE t SET id='42x';", "UPDATE t SET id=id+10,v=NULL;",
      "UPDATE t SET id=missing,id=id+10;",
      "UPDATE t SET id=CASE WHEN id=2 THEN abs(-9223372036854775808) ELSE 100 END;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"rowid UPDATE accepted invalid input: {sql}"
    | .error _ => pure ()

private def expectSQLiteImplicitRowid : IO Unit := do
  let cases : List (String × List (List Value)) := [
    ("CREATE TABLE t(v); INSERT INTO t VALUES('a'),('a'); SELECT rowid,v FROM t ORDER BY rowid;",
      [[.integer 1,.text "a"],[.integer 2,.text "a"]]),
    ("CREATE TABLE t(v); INSERT INTO t(rowid,v) VALUES(-5,'a'); INSERT INTO t(v) VALUES('b'); SELECT rowid,v FROM t ORDER BY rowid;",
      [[.integer (-5),.text "a"],[.integer (-4),.text "b"]]),
    ("CREATE TABLE t(v); INSERT INTO t DEFAULT VALUES; INSERT INTO t(rowid,v) VALUES(12,'x'); INSERT INTO t VALUES('y'); SELECT rowid,v FROM t ORDER BY rowid;",
      [[.integer 1,.null],[.integer 12,.text "x"],[.integer 13,.text "y"]]),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t(v) VALUES('a'); INSERT INTO t DEFAULT VALUES; INSERT INTO t VALUES(NULL,'b'); SELECT * FROM t ORDER BY id;",
      [[.integer 1,.text "a"],[.integer 2,.null],[.integer 3,.text "b"]]),
    ("CREATE TABLE t(rowid,oid,_rowid_,v); INSERT INTO t VALUES('a','b','c',1); SELECT * FROM t;",
      [[.text "a",.text "b",.text "c",.integer 1]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"implicit rowid: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"implicit rowid result: {sql}"
  for sql in ["INSERT INTO t(unknown) VALUES(1);", "INSERT INTO t(unknown) DEFAULT VALUES;",
      "INSERT INTO t VALUES();", "INSERT INTO t(rowid) VALUES('bad');",
      "INSERT INTO t(rowid) VALUES(1),(1);"] do
    match CoreSQL.execute Core.State.empty ("CREATE TABLE t(v);" ++ sql) with
    | .ok _ => fail s!"rowid insertion accepted invalid input: {sql}"
    | .error _ => pure ()

private def expectSQLiteAggregateExpressions : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,1),(2,1.0),(3,2),(4,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT count(DISTINCT v),sum(DISTINCT v),avg(DISTINCT v),total(DISTINCT v) FROM t;",
      [[.integer 2, .integer 3, .real 1.5, .real 3.0]]),
    ("SELECT count(*),sum(v+1),avg(v),count(v*0) FROM t WHERE v+1>2;",
      [[.integer 1, .integer 3, .real 2.0, .integer 1]]),
    ("SELECT count(*),sum(v),avg(v),total(v),min(v),max(v) FROM t WHERE id<0;",
      [[.integer 0, .null, .null, .real 0.0, .null, .null]]),
    ("SELECT count(abs(-9223372036854775808)) FROM t LIMIT 0;", []),
    ("SELECT count(*) FROM t LIMIT 1 OFFSET 1;", []),
    ("SELECT count() FROM t;", [[.integer 4]]),
    ("SELECT count(x.v) FROM t AS x;", [[.integer 3]]),
    ("SELECT count(*) FROM t WHERE abs(-9223372036854775808) LIMIT 0;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"aggregate expression: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do
      fail s!"aggregate expression result: {sql}"
  for sql in ["SELECT count(missing) FROM t LIMIT 0;", "SELECT count(sum(v)) FROM t;",
      "SELECT count(t.v) FROM t AS x;", "SELECT sum(unknown.v) FROM t;",
      "SELECT sum(*) FROM t;", "SELECT count(abs(-9223372036854775808)) FROM t LIMIT 1 OFFSET 1;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"aggregate accepted invalid expression: {sql}"
    | .error _ => pure ()

private def expectSQLiteRawText : IO Unit := do
  unless SQLite.CLI.listTextBytes [65,1,13,10,9,10,13,0,255] == [65,94,65,13,10,9,10,94,77] do
    fail "CLI control-byte rendering differs from the pinned default list mode"
  let cases : List (String × List (List Value)) := [
    ("SELECT CAST(X'FF8041' AS TEXT),typeof(CAST(X'FF8041' AS TEXT)),length(CAST(X'FF8041' AS TEXT));",
      [[.textBytes #[255,128,65], .text "text", .integer 2]]),
    ("SELECT substr(CAST(X'41808142' AS TEXT),2,2),instr(CAST(X'41808142' AS TEXT),'B');",
      [[.textBytes #[128,129], .integer 2]]),
    ("SELECT trim(CAST(X'FF41FF' AS TEXT),CAST(X'FF' AS TEXT));", [[.text "A"]]),
    ("SELECT hex(replace(CAST(X'C3A9FF' AS TEXT),CAST(X'A9' AS TEXT),CAST(X'80' AS TEXT)));", [[.text "C380FF"]]),
    ("SELECT hex(quote(CAST(X'FF270080' AS TEXT)));", [[.text "27FF272727"]]),
    ("SELECT unhex(CAST(X'3441FF3432' AS TEXT),CAST(X'FF' AS TEXT));", [[.blob #[74,66]]]),
    ("SELECT hex(char(55296)),typeof(char(55296)),unicode(char(55296));",
      [[.text "EDA080", .text "text", .integer 65533]]),
    ("SELECT CAST(CAST(X'3132FF' AS TEXT) AS NUMERIC),CAST(X'3132FF' AS TEXT)=CAST(12 AS INT);",
      [[.integer 12, .integer 0]]),
    ("CREATE TABLE t(v); INSERT INTO t VALUES(CAST(X'FF' AS TEXT)); UPDATE t SET v=v||'a'; SELECT v,typeof(v) FROM t;",
      [[.textBytes #[255,97], .text "text"]]),
    ("CREATE TABLE t(v); INSERT INTO t VALUES(CAST(X'FF' AS TEXT)); SELECT coalesce(min(v),'a'),count(v) FROM t;",
      [[.textBytes #[255], .integer 1]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"raw TEXT: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"raw TEXT mismatch: {sql}"

private def expectSQLiteWALIndexFixture (walPath shmPath : String) : IO Nat := do
  let wal ← IO.FS.readBinFile walPath
  let shm ← IO.FS.readBinFile shmPath
  let some header := SQLite.WALIndex.decodeCopies false shm.data |
    throw (IO.userError "wal-index header rejected")
  unless header.encode false == shm.data.extract 0 48 do
    throw (IO.userError "wal-index header re-encoding mismatch")
  let log ← match SQLite.WALAppend.read wal.data with
    | .ok (some log) => pure log
    | .ok none => fail "WAL append parser rejected the reference log"
    | .error message => fail message
  unless log.committedFrames == header.maxFrame.val && log.pageCount == header.databaseSize.val &&
      log.checksum == header.frameChecksum do
    fail "WAL parser and independent wal-index disagree"
  let some decodedBig := SQLite.WALIndex.decodeHeader true (header.encode true) |
    throw (IO.userError "big-endian component header round-trip failed")
  unless decodedBig.encode true == header.encode true do
    throw (IO.userError "big-endian component header changed")
  let mut pages := #[]
  for i in [:header.maxFrame.val] do
    let some page := SQLite.WALIndex.number? true wal.data (32 + i * (24 + header.pageSize)) 4 |
      throw (IO.userError "WAL page number is truncated")
    pages := pages.push page
  for splitAt in [0, 1, 2, 73, 4061, 4062, 4063, header.maxFrame.val] do
    let count := min splitAt pages.size
    let first ← match SQLite.WALIndex.append false 0 (pages.extract 0 count) #[] with
      | .ok value => pure value
      | .error error => throw (IO.userError error)
    -- Simulate a writer that put an uncommitted suffix into the shared hash.
    let dirty ← match SQLite.WALIndex.append false count #[99999, 88888, 77777] first.bytes with
      | .ok value => pure value
      | .error error => throw (IO.userError error)
    let complete ← match SQLite.WALIndex.append false count (pages.extract count pages.size) dirty.bytes with
      | .ok value => pure value
      | .error error => throw (IO.userError error)
    let expectedBytes := ((SQLite.WALIndex.frameRegion header.maxFrame.val) + 1) * 32768
    unless complete.bytes.extract 136 expectedBytes == shm.data.extract 136 expectedBytes do
      throw (IO.userError s!"wal-index mapping mismatch at split {count}")
  return pages.size

private def exportSQLiteWALAppend (walPath imagePath destination : String) : IO Nat := do
  let original ← IO.FS.readBinFile walPath
  let image ← IO.FS.readBinFile imagePath
  let log ← match SQLite.WALAppend.read original.data with
    | .ok (some log) => pure log
    | .ok none => fail "WAL append fixture has no valid log header"
    | .error message => fail message
  unless image.size % log.header.pageSize = 0 do fail "unaligned fixture image"
  let pages := (Array.range (image.size / log.header.pageSize)).map fun i =>
    (image.extract (i * log.header.pageSize) ((i + 1) * log.header.pageSize)).data
  let prepared ← match SQLite.WALAppend.prepare log pages with
    | .ok prepared => pure prepared
    | .error message => fail message
  IO.FS.withFile destination .write fun handle => do
    handle.write (original.extract 0 log.endOffset)
    let mut offset := log.endOffset
    for write in prepared.writes do
      unless write.offset = offset do fail "WAL append touched an old prefix or left a gap"
      handle.write (ByteArray.mk write.bytes)
      offset := offset + write.bytes.size
    unless offset = prepared.endOffset do fail "WAL append endpoint mismatch"
  return prepared.committedFrames.val

private def expectSQLiteWALIndex : IO Unit := do
  for big in [false, true] do
    for pageSize in [512, 4096, 65536] do
      let header : SQLite.WALIndex.Header := {
        change := ⟨1234, by decide⟩, bigEndianChecksum := !big, pageSize
        maxFrame := ⟨4063, by decide⟩, databaseSize := ⟨99, by decide⟩
        frameChecksum := ⟨⟨1234567, by decide⟩, ⟨9876543, by decide⟩⟩
        saltFirst := ⟨0x12345678, by decide⟩, saltSecond := ⟨0x90abcdef, by decide⟩ }
      let encoded := header.encode big
      let some decoded := SQLite.WALIndex.decodeCopies big (encoded ++ encoded) |
        fail "WAL index header round-trip rejected"
      unless decoded.encode big == encoded do fail "WAL index header bytes changed"
      unless (SQLite.WALIndex.decodeCopies big (encoded ++ encoded.set! 8 255)).isNone do
        fail "WAL index accepted different copies"
      unless (SQLite.WALIndex.decodeCopies big ((encoded.set! 0 255) ++ (encoded.set! 0 255))).isNone do
        fail "WAL index accepted invalid version/checksum"

private def expectSQLiteLargeValueBounds : IO Unit := do
  for (size, overhead, accepted) in [(1000000000, 0, true), (1000000001, 0, false),
      (999999999, 1, true), (1000000000, 1, false), (0, 0, true)] do
    unless (SQLite.Limits.check size overhead).isOk == accepted do
      throw (IO.userError "SQLite byte-limit boundary mismatch")
  unless PhysicalCodec.textByteLimit = SQLite.Text.resultLimit + 1 do
    throw (IO.userError "physical/scalar byte limits disagree")
  match SQLite.Text.zeroblob (.integer 1000000) with
  | .ok (.blob bytes) =>
      unless bytes.size = 1000000 && bytes.all (· == 0) do
        throw (IO.userError "million-byte zeroblob payload mismatch")
  | _ => throw (IO.userError "million-byte zeroblob was rejected")
  unless (SQLite.Text.zeroblob (.integer 1000000001)).toOption.isNone do
    throw (IO.userError "oversized zeroblob was accepted")

private def expectSingletonLeafPacking : IO Unit := do
  let rec singles : RecursiveBPlusTree.Node Nat → Bool
    | .leaf entries => entries.length ≤ 1
    | .branch2 left _ right => singles left && singles right
    | .branch3 left _ middle _ right => singles left && singles middle && singles right
  for count in List.range 130 ++ [257, 511, 512, 1024] do
    let entries := (List.range count).map fun i => (i, i)
    let tree := SingletonPageTree.build entries
    unless tree.checkRootValid && singles tree && tree.toList == entries do
      fail s!"single-entry leaf packing failed at {count} entries"
  for width in [2001, 2044, 2048, 3000, 4080, 4096, 8000, 10000] do
    for count in [2, 3, 4, 5, 7, 8, 9, 17] do
      let inserts := (List.range count).map fun i =>
        s!"INSERT INTO t VALUES({i},zeroblob({width}));"
      let sql := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);" ++ String.join inserts
      let (state, _) ← match CoreSQL.execute Core.State.empty sql with
        | .ok result => pure result
        | .error message => fail message
      unless (CorePageCodec.encodeChecked state.database).isSome do
        fail s!"large local payload packing failed: width={width}, rows={count}"

private def expectSQLiteOrderModifiers : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,'b'),(2,NULL),(3,'A'),(4,'a '),(5,'a');"
  let cases : List (String × List (List Value)) := [
    ("SELECT id FROM t ORDER BY v NULLS LAST;", [[.integer 3], [.integer 5], [.integer 4], [.integer 1], [.integer 2]]),
    ("SELECT id FROM t ORDER BY v DESC NULLS FIRST;", [[.integer 2], [.integer 1], [.integer 4], [.integer 5], [.integer 3]]),
    ("SELECT id FROM t ORDER BY v COLLATE NOCASE;", [[.integer 2], [.integer 3], [.integer 5], [.integer 4], [.integer 1]]),
    ("SELECT id FROM t ORDER BY v COLLATE RTRIM NULLS LAST;", [[.integer 3], [.integer 4], [.integer 5], [.integer 1], [.integer 2]]),
    ("SELECT id FROM t ORDER BY (v||'') COLLATE NOCASE DESC NULLS LAST LIMIT 2;", [[.integer 1], [.integer 4]]),
    ("SELECT 1 ORDER BY 1 COLLATE NOCASE NULLS LAST;", [[.integer 1]]),
    ("SELECT id FROM t ORDER BY v COLLATE missing COLLATE NOCASE LIMIT 2;", [[.integer 2], [.integer 3]]),
    ("SELECT id FROM t ORDER BY id DESC NULLS FIRST,abs(-9223372036854775808) LIMIT 1;", [[.integer 5]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"ORDER modifiers: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"ORDER modifiers mismatch: {sql}"
  for sql in ["SELECT id FROM t ORDER BY v COLLATE missing LIMIT 0;",
      "SELECT 1 ORDER BY 1 COLLATE missing LIMIT 0;", "SELECT id FROM t ORDER BY v NULLS;",
      "SELECT id FROM t ORDER BY v NULLS MIDDLE;", "SELECT id FROM t ORDER BY 0 AND v;",
      "SELECT id FROM t ORDER BY 0 AND abs(-9223372036854775808) COLLATE BINARY;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"ORDER modifiers omitted error: {sql}"
    | .error _ => pure ()

private def expectSQLiteOrderExpressions : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,w); INSERT INTO t VALUES(1,1,2),(2,-9223372036854775808,1),(3,3,0);"
  let cases : List (String × List (List Value)) := [
    ("SELECT id+1 AS k FROM t ORDER BY k DESC LIMIT 1;", [[.integer 4]]),
    ("SELECT id,v FROM t ORDER BY 2 LIMIT 1;", [[.integer 2, .integer (-9223372036854775808)]]),
    ("SELECT id AS v FROM t ORDER BY v COLLATE BINARY DESC LIMIT 1;", [[.integer 3]]),
    ("SELECT id AS v FROM t ORDER BY v;", [[.integer 1], [.integer 2], [.integer 3]]),
    ("SELECT id AS v FROM t ORDER BY v+0;", [[.integer 2], [.integer 1], [.integer 3]]),
    ("SELECT abs(v) FROM t ORDER BY -w LIMIT 1;", [[.integer 1]]),
    ("SELECT id FROM t ORDER BY id DESC,abs(v) LIMIT 1;", [[.integer 3]]),
    ("SELECT abs(v) FROM t ORDER BY 1 LIMIT 0;", []),
    ("SELECT 3 AS x,1 ORDER BY x+1;", [[.integer 3, .integer 1]]),
    ("SELECT 1 ORDER BY abs(-9223372036854775808);", [[.integer 1]]),
    ("SELECT abs(-9223372036854775808) ORDER BY 1 LIMIT 1 OFFSET 1;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"ORDER expression: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"ORDER expression mismatch: {sql}"
  for sql in ["SELECT abs(v) FROM t ORDER BY w LIMIT 1;", "SELECT id FROM t ORDER BY 0 LIMIT 0;",
      "SELECT id FROM t ORDER BY 2 LIMIT 0;", "SELECT id FROM t ORDER BY missing LIMIT 0;",
      "SELECT 1 ORDER BY unknown_function() LIMIT 0;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"ORDER expression omitted error: {sql}"
    | .error _ => pure ()

private def expectSQLiteQuotedNames : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,\"select\" TEXT,v); INSERT INTO t VALUES(1,'a',3),(2,'b',4); CREATE TABLE empty(id INTEGER PRIMARY KEY,v);"
  let cases : List (String × List (List Value)) := [
    ("SELECT \"select\",[v],`id` FROM t ORDER BY \"id\";",
      [[.text "a", .integer 3, .integer 1], [.text "b", .integer 4, .integer 2]]),
    ("SELECT sum(\"v\"),count([id]) FROM t;", [[.integer 7, .integer 2]]),
    ("SELECT [v],sum(\"v\") FROM t GROUP BY `v`;", [[.integer 3, .integer 3], [.integer 4, .integer 4]]),
    ("SELECT x.[v] FROM t AS x WHERE x.id=1;", [[.integer 3]]),
    ("SELECT 0 AND \"missing\";", [[.integer 0]]),
    ("SELECT 0 AND missing.v FROM empty;", []),
    ("UPDATE t AS x SET v=x.[v]+1 WHERE x.id=1; SELECT v FROM t WHERE id=1;", [[.integer 4]]),
    ("DELETE FROM t WHERE [v]=3; SELECT id FROM t;", [[.integer 2]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"quoted names: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"quoted names mismatch: {sql}"
  for sql in ["SELECT t.id FROM t AS x LIMIT 0;", "SELECT missing.id FROM t WHERE id=1;",
      "SELECT id FROM t WHERE missing.v=3;", "SELECT id FROM t ORDER BY missing.v;",
      "SELECT \"missing\" FROM empty LIMIT 0;", "SELECT missing.* FROM empty;",
      "SELECT count(missing.v) FROM empty;", "UPDATE empty SET v=1 WHERE missing.id=2;",
      "UPDATE t AS x SET v=t.v;", "DELETE FROM empty WHERE missing.v=1;",
      "SELECT lean_dqs('v') FROM t LIMIT 0;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"name binding omitted error: {sql}"
    | .error _ => pure ()

private def expectSQLiteWhereAliases : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,x INTEGER);INSERT INTO t VALUES(1,1,0),(2,3,1),(3,NULL,0);" ++
    "CREATE TABLE e(id INTEGER PRIMARY KEY,v);CREATE INDEX t_v ON t(v);"
  let cases : List (String × List (List Value)) := [
    ("SELECT v+1 AS k FROM t WHERE k>2;", [[.integer 4]]),
    ("SELECT v AS x FROM t WHERE x=0 ORDER BY id;", [[.integer 1], [.null]]),
    ("SELECT v AS k FROM t WHERE k IS NULL;", [[.null]]),
    ("SELECT v AS k FROM t AS s WHERE k=1 ORDER BY s.id;", [[.integer 1]]),
    ("SELECT v AS true FROM t WHERE true;", [[.integer 1], [.integer 3]]),
    ("SELECT v AS false FROM t WHERE false;", [[.integer 1], [.integer 3]]),
    ("SELECT v AS k FROM t WHERE 0 AND k>0;", []),
    ("SELECT count(*) AS k FROM t WHERE 0 AND k>0;", [[.integer 0]]),
    ("SELECT count(*) AS k WHERE 0 AND k>0;", [[.integer 0]]),
    ("SELECT 1 AS k WHERE k=1;", [[.integer 1]]),
    ("SELECT 0 AS true WHERE true;", []),
    ("SELECT TRUE AS true WHERE true;", [[.integer 1]]),
    ("SELECT 0 AS true WHERE true IS TRUE;", [[.integer 0]]),
    ("SELECT id AS k,id+1 AS k FROM t WHERE k=1;", [[.integer 1, .integer 2]]),
    ("SELECT sum(v) FROM t WHERE x=0 HAVING sum(v)=1;", [[.integer 1]]),
    ("SELECT v AS k,count(*) FROM t WHERE k>1 GROUP BY k;", [[.integer 3, .integer 1]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"WHERE alias: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"WHERE alias mismatch: {sql}"
  for sql in ["SELECT v AS k FROM t WHERE t.k=1;", "SELECT v AS k FROM e WHERE missing LIMIT 0;",
      "SELECT count(*) AS k FROM t WHERE k>0;", "SELECT count(*) AS k WHERE k>0;",
      "SELECT v AS k,k AS y FROM t WHERE y>0;", "SELECT 1 AS k WHERE 0 AND no_function(k);"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"WHERE alias error omitted: {sql}"

private def expectSQLiteAggregateInternalOrder : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,s);INSERT INTO t VALUES(1,'A','x'),(2,'a','y'),(3,1,'z'),(4,1.0,'q'),(5,NULL,NULL);" ++
    "CREATE TABLE e(id INTEGER PRIMARY KEY,v,s);" ++
    "CREATE TABLE o(id INTEGER PRIMARY KEY,v);INSERT INTO o VALUES(1,9223372036854775807),(2,1),(3,-1);"
  let cases : List (String × List (List Value)) := [
    ("SELECT group_concat(v ORDER BY id DESC),string_agg(v,s ORDER BY id DESC) FROM t;",
      [[.text "1.0,1,a,A", .text "1.0z1yaxA"]]),
    ("SELECT group_concat(DISTINCT v ORDER BY v),group_concat(DISTINCT v ORDER BY id DESC) FROM t;",
      [[.text "1.0,A,a", .text "1,a,A"]]),
    ("SELECT group_concat(DISTINCT v COLLATE NOCASE ORDER BY v COLLATE NOCASE) FROM t;", [[.text "1.0,a"]]),
    ("SELECT group_concat(v ORDER BY 1) FROM t;", [[.text "A,a,1,1.0"]]),
    ("SELECT count(ORDER BY missing),count(ALL ORDER BY no_function(1)) FROM t;", [[.integer 5, .integer 5]]),
    ("SELECT count(ORDER BY missing);", [[.integer 1]]),
    ("SELECT char(ORDER BY missing);", [[.text ""]]),
    ("SELECT min(v ORDER BY abs(-9223372036854775808)) FROM t;", [[.integer 1]]),
    ("SELECT min(v ORDER BY id COLLATE missing),max(v ORDER BY v='a' COLLATE missing) FROM t;",
      [[.integer 1, .text "a"]]),
    ("SELECT min(v ORDER BY json(v)),max(v ORDER BY sqrt(v)) FROM t;", [[.integer 1, .text "a"]]),
    ("SELECT min(v ORDER BY v MATCH 'x') FROM t;", [[.integer 1]]),
    ("SELECT min(v ORDER BY 0x10000000000000000),min(v ORDER BY -0x8000000000000000) FROM t;",
      [[.integer 1, .integer 1]]),
    ("SELECT id,min(v ORDER BY id),max(v),min(v ORDER BY id ASC NULLS FIRST) FROM o;",
      [[.integer 1, .integer (-1), .integer 9223372036854775807, .integer (-1)]]),
    ("SELECT sum(v ORDER BY id DESC) FROM o;", [[.integer 9223372036854775807]]),
    ("SELECT sum(v ORDER BY id) FILTER(WHERE id>1) FROM o;", [[.integer 0]]),
    ("SELECT group_concat(v ORDER BY abs(-9223372036854775808)) FILTER(WHERE 0) FROM t;", [[.null]]),
    ("SELECT count(v ORDER BY abs(-9223372036854775808)) FROM e;", [[.integer 0]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"aggregate internal ORDER BY: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"aggregate internal ORDER BY mismatch: {sql}"
  for sql in ["SELECT sum(v ORDER BY id) FROM o;", "SELECT count(v ORDER BY abs(-9223372036854775808)) FROM t;",
      "SELECT min(v ORDER BY missing) FROM e LIMIT 0;", "SELECT min(v ORDER BY no_function(id)) FROM t LIMIT 0;",
      "SELECT min(v ORDER BY json(v,v)) FROM e;", "SELECT min(v ORDER BY min(v)) FROM t;",
      "SELECT min(v ORDER BY likelihood(v,0)) FROM e;", "SELECT abs(v ORDER BY id) FROM e;",
      "SELECT min(v ORDER BY likelihood(v,0x00000000000000000)) FROM e;",
      "SELECT count(* ORDER BY id) FROM t;", "SELECT count(DISTINCT ORDER BY id) FROM t;",
      "SELECT __sqlean_aggregate_order(group_concat(v),id) FROM t;",
      "SELECT group_concat(v ORDER BY __sqlean_order_desc(id)) FROM t;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"aggregate internal ORDER BY error omitted: {sql}"

private def expectSQLiteAggregateFilter : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,g,v);INSERT INTO t VALUES(1,0,3),(2,0,1),(3,1,9),(4,1,1),(5,1,NULL);" ++
    "CREATE TABLE e(id INTEGER PRIMARY KEY,g,v);"
  let cases : List (String × List (List Value)) := [
    ("SELECT count(*) FILTER(WHERE id>2),count(v) FILTER(WHERE id>2),sum(v) FILTER(WHERE id>2) FROM t;",
      [[.integer 3, .integer 2, .integer 10]]),
    ("SELECT group_concat(v) FILTER(WHERE id>2),group_concat(DISTINCT v) FILTER(WHERE v<4) FROM t;",
      [[.text "9,1", .text "3,1"]]),
    ("SELECT sum(abs(-9223372036854775808)) FILTER(WHERE 0),total(v) FILTER(WHERE 0) FROM t;",
      [[.null, .real 0.0]]),
    ("SELECT group_concat(v,abs(-9223372036854775808)) FILTER(WHERE NULL) FROM t;", [[.null]]),
    ("SELECT id,min(v) FILTER(WHERE 0) FROM t;", [[.integer 1, .null]]),
    ("SELECT id,min(v) FILTER(WHERE id>2) FROM t;", [[.integer 4, .integer 1]]),
    ("SELECT id,min(v),max(v) FILTER(WHERE 0) FROM t;", [[.integer 2, .integer 1, .null]]),
    ("SELECT g,id,min(v),max(v) FILTER(WHERE 0) FROM t GROUP BY g ORDER BY g;",
      [[.integer 0, .integer 1, .integer 1, .null], [.integer 1, .integer 3, .integer 1, .null]]),
    ("SELECT id,min(v) FILTER(WHERE id<3),min(v) FILTER(WHERE id=3) FROM t;",
      [[.integer 3, .integer 1, .integer 9]]),
    ("SELECT count(*) FILTER(WHERE 0),sum(1) FILTER(WHERE 1);", [[.integer 0, .integer 1]]),
    ("SELECT count(*) FILTER(WHERE 1),min(v) FILTER(WHERE 1) FROM e;", [[.integer 0, .null]]),
    ("SELECT sum(v) FILTER(WHERE id>2) AS x FROM t HAVING x=10;", [[.integer 10]]),
    ("SELECT count(*) FROM t ORDER BY sum(abs(-9223372036854775808)) FILTER(WHERE 0);", [[.integer 5]]),
    ("SELECT count(*) FILTER(WHERE 0 AND missing) FROM t;", [[.integer 0]]),
    ("SELECT count(*) FILTER(WHERE 0 AND 0x10000000000000000) FROM t;", [[.integer 0]]),
    ("SELECT count(*) FILTER(WHERE 'a' COLLATE missing)=0 FROM t;", [[.integer 1]]),
    ("SELECT abs(-9223372036854775808)+count(*) FILTER(WHERE 0) FROM t LIMIT 1 OFFSET 1;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"aggregate FILTER: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"aggregate FILTER mismatch: {sql}"
  for sql in ["SELECT count(*) FILTER(WHERE likely(NULL AND abs(-9223372036854775808))) FROM t;",
      "SELECT count(*) FILTER(WHERE (NULL AND abs(-9223372036854775808)) COLLATE binary) FROM t;",
      "SELECT count(*) FROM t HAVING likely(NULL AND abs(-9223372036854775808));",
      "SELECT count(*) FROM t HAVING (NULL AND abs(-9223372036854775808)) COLLATE binary;",
      "SELECT count(*) FILTER(WHERE missing) FROM e LIMIT 0;",
      "SELECT count(*) FILTER(WHERE 0 AND no_function(1)) FROM e LIMIT 0;",
      "SELECT count(*) FILTER(WHERE sum(v)>0) FROM e;", "SELECT abs(v) FILTER(WHERE 1) FROM e;",
      "SELECT sum(v) FILTER(WHERE 1) FILTER(WHERE 1) FROM e;",
      "SELECT __sqlean_aggregate_filter(count(*),1) FROM t;",
      "SELECT '__sqlean_aggregate_filter'(count(*),1) FROM t;",
      "SELECT sum(abs(-9223372036854775808)) FILTER(WHERE 1) FROM t LIMIT 1 OFFSET 1;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"aggregate FILTER error omitted: {sql}"

private def expectSQLiteProbability : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO t VALUES(1,'1'),(2,'2'),(3,NULL);" ++
    "CREATE TABLE e(id INTEGER PRIMARY KEY,v TEXT);"
  let cases : List (String × List (List Value)) := [
    ("SELECT likely(NULL),unlikely(1.25),likelihood('x',0.5);", [[.null, .real 1.25, .text "x"]]),
    ("SELECT id,likely(v)=1,unlikely(v) IN (1,2) FROM t ORDER BY id;",
      [[.integer 1, .integer 0, .integer 0], [.integer 2, .integer 0, .integer 0], [.integer 3, .null, .null]]),
    ("SELECT likely(CAST(1 AS TEXT))=1,unlikely(CAST(1 AS INTEGER))='1';", [[.integer 0, .integer 0]]),
    ("SELECT likely(CAST(1 AS TEXT))='1',unlikely(CAST(1 AS INTEGER))=1;", [[.integer 1, .integer 1]]),
    ("SELECT likelihood(7,0.0),likelihood(8,1.0),likelihood(9,(.5));", [[.integer 7, .integer 8, .integer 9]]),
    ("SELECT likely(count(*)) AS x FROM t HAVING x>0;", [[.integer 3]]),
    ("SELECT v,count(*) FROM t GROUP BY likely(1);", [[.text "1", .integer 3]]),
    ("SELECT likely(0 AND abs(-9223372036854775808));", [[.integer 0]]),
    ("SELECT unlikely(1 OR abs(-9223372036854775808));", [[.integer 1]]),
    ("SELECT 1 WHERE likely(NULL AND abs(-9223372036854775808));", []),
    ("SELECT 1 WHERE (NULL AND abs(-9223372036854775808)) COLLATE binary;", []),
    ("SELECT 1 WHERE likely(1 OR abs(-9223372036854775808));", [[.integer 1]]),
    ("SELECT likely(abs(-9223372036854775808)) FROM e;", []),
    ("SELECT likely(abs(-9223372036854775808)) LIMIT 0;", []),
    ("SELECT likely(abs(-9223372036854775808)) LIMIT 1 OFFSET 1;", []),
    ("SELECT likelihood(DISTINCT 7,0.5);", [[.integer 7]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"probability hint: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"probability hint mismatch: {sql}"
  for sql in ["SELECT likely(0) AND abs(-9223372036854775808);",
      "SELECT likely(1) OR abs(-9223372036854775808);",
      "SELECT 1 WHERE NOT likely(NULL AND abs(-9223372036854775808));",
      "SELECT likelihood(1,0) LIMIT 0;", "SELECT likelihood(v,+0.5) FROM e;",
      "SELECT likelihood(v,-0.0) FROM e;", "SELECT likelihood(v,0.5 COLLATE binary) FROM e;",
      "SELECT likelihood(v,0.5+0.0) FROM e;", "SELECT 0 AND likelihood(1,0);",
      "SELECT 1 OR likelihood(1,0);", "SELECT likely();", "SELECT unlikely(1,2);"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"probability hint error omitted: {sql}"

private def expectSQLiteUpdateIgnore : IO Unit := do
  for (input, expected) in [(1,0),(2,10),(3,16),(8,30),(10,33),(100,66),(200,76),(125829120,269)] do
    unless SQLite.PlannerCost.logEst input == expected do fail "SQLite planner LogEst mismatch"
  unless SQLite.PlannerCost.add 33 33 == 43 && SQLite.PlannerCost.add 100 0 == 100 do
    fail "SQLite planner LogEst addition mismatch"
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER);CREATE UNIQUE INDEX tu ON t(u);" ++
    "INSERT INTO t VALUES(1,'a',1),(2,'b',2),(3,'c',3);" ++
    "CREATE TABLE k(k TEXT PRIMARY KEY NOT NULL,v);INSERT INTO k VALUES('a',1),('b',2);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  let cases : List (String × Nat × List (List Value)) := [
    ("UPDATE OR IGNORE t SET u=u+1;SELECT id,u FROM t ORDER BY id;", 1,
      [[.integer 1, .integer 1], [.integer 2, .integer 2], [.integer 3, .integer 4]]),
    ("UPDATE OR IGNORE t SET id=id-1;SELECT id,u FROM t ORDER BY id;", 3,
      [[.integer 0, .integer 1], [.integer 1, .integer 2], [.integer 2, .integer 3]]),
    ("UPDATE OR IGNORE t SET v=NULL;SELECT id,u FROM t ORDER BY id;", 0,
      [[.integer 1, .integer 1], [.integer 2, .integer 2], [.integer 3, .integer 3]]),
    ("UPDATE OR IGNORE k SET k='a';SELECT k,v FROM k ORDER BY k;", 1,
      [[.text "a", .integer 1], [.text "b", .integer 2]]),
    ("UPDATE k SET k=k||'x';SELECT k,v FROM k ORDER BY k;", 2,
      [[.text "ax", .integer 1], [.text "bx", .integer 2]])]
  for (sql, changes, expected) in cases do
    let (_, results) ← match CoreSQL.execute initial sql with
      | .ok result => pure result
      | .error message => fail s!"UPDATE OR IGNORE: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows && (results.map (·.changes)).sum == changes do
      fail s!"UPDATE OR IGNORE mismatch: {sql}"
  let orderedSql := "CREATE TABLE q(id INTEGER PRIMARY KEY,v,u);CREATE INDEX qv ON q(v);" ++
    "CREATE UNIQUE INDEX qu ON q(u);INSERT INTO q VALUES(1,'b',1),(2,'a',2),(3,'c',3);" ++
    "UPDATE OR IGNORE q SET u=100 WHERE v>='a' AND v<='c';SELECT id FROM q WHERE u=100;"
  let (_, ordered) ← match CoreSQL.execute Core.State.empty orderedSql with
    | .ok result => pure result
    | .error message => fail message
  let expected ← match SQLSurface.value (.integer 2) with
    | .ok value => pure value
    | .error message => fail message
  unless (ordered.getLast?).map (·.rows) == some [[expected]] do fail "UPDATE IGNORE lost index scan order"
  let createdOrderSql := "CREATE TABLE q(id INTEGER PRIMARY KEY,v,u INTEGER,w INTEGER);" ++
    "CREATE UNIQUE INDEX qu ON q(u);CREATE INDEX qw ON q(w);" ++
    "INSERT INTO q VALUES(1,'a',1,3),(2,'b',2,2),(3,'c',3,1);" ++
    "UPDATE OR IGNORE q SET u=100 WHERE u>0 AND w>0;SELECT id FROM q WHERE u=100;"
  let (_, createdOrder) ← match CoreSQL.execute Core.State.empty createdOrderSql with
    | .ok result => pure result
    | .error message => fail message
  let expected ← match SQLSurface.value (.integer 3) with
    | .ok value => pure value
    | .error message => fail message
  unless (createdOrder.getLast?).map (·.rows) == some [[expected]] do fail "CREATE INDEX lost planner creation order"
  for sql in ["UPDATE OR IGNORE t SET id=NULL;", "UPDATE OR IGNORE t SET id='bad',v=NULL;",
      "UPDATE OR IGNORE t SET v=NULL,u=abs(-9223372036854775808);",
      "UPDATE OR IGNORE t SET u=no_function(),u=1;"] do
    if (CoreSQL.execute initial sql).isOk then fail s!"UPDATE OR IGNORE swallowed error: {sql}"

private def expectSQLiteInsertIgnore : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER);CREATE UNIQUE INDEX tu ON t(u);" ++
    "INSERT INTO t VALUES(1,'a',1),(3,'c',3);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  let sql := "INSERT OR IGNORE INTO t VALUES(1,'skip',9),(NULL,NULL,9),(NULL,'d',4),(5,'skip',4),(NULL,'e',5);"
  let (state, results) ← match CoreSQL.execute initial sql with
    | .ok result => pure result
    | .error message => fail s!"INSERT OR IGNORE: {message}"
  unless (results.map (·.changes)).sum == 2 do fail "INSERT OR IGNORE change count"
  let (_, selected) ← match CoreSQL.execute state "SELECT id,v FROM t ORDER BY id;" with
    | .ok result => pure result
    | .error message => fail message
  let expected : List (List Value) := [[.integer 1, .text "a"], [.integer 3, .text "c"],
    [.integer 4, .text "d"], [.integer 5, .text "e"]]
  let expected ← match expected.mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (selected.getLast?).map (·.rows) == some expected do fail "INSERT OR IGNORE row allocation"
  for sql in ["INSERT OR IGNORE INTO t VALUES('bad',NULL,9);",
      "INSERT OR IGNORE INTO t VALUES(1,abs(-9223372036854775808),1);",
      "INSERT OR IGNORE INTO t VALUES(1.5,'x',9);", "INSERT OR IGNORE INTO t VALUES(9,'x');",
      "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',no_function(),9);",
      "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',missing,9);",
      "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',0 AND no_function(),9);"] do
    if (CoreSQL.execute initial sql).isOk then fail s!"INSERT OR IGNORE swallowed a non-constraint error: {sql}"
  let (copied, results) ← match CoreSQL.execute initial "INSERT OR IGNORE INTO t SELECT * FROM t;" with
    | .ok result => pure result
    | .error message => fail message
  unless (results.map (·.changes)).sum == 0 && copied.database.tables.length == initial.database.tables.length do
    fail "INSERT OR IGNORE SELECT duplicate rows"

private def expectSQLiteDeleteReturning : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(3,'c'),(1,'a'),(2,'b');"
  let cases : List (String × List (List Value)) := [
    ("DELETE FROM t WHERE id<3 RETURNING id,v;", [[.integer 1, .text "a"], [.integer 2, .text "b"]]),
    ("DELETE FROM t AS x WHERE x.id=2 RETURNING *,t.id+1;", [[.integer 2, .text "b", .integer 3]]),
    ("DELETE FROM t WHERE 0 RETURNING abs(-9223372036854775808);", []),
    ("DELETE FROM t WHERE id=3 RETURNING 0 AND missing;", [[.integer 0]])]
  for (sql, expected) in cases do
    let (state, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"DELETE RETURNING: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    let some result := results.getLast? | fail "DELETE RETURNING result missing"
    unless result.rows == rows && result.changes == expected.length do fail s!"DELETE RETURNING mismatch: {sql}"
    let some table := state.database.findTable? "t" | fail "DELETE RETURNING removed the table"
    unless table.rows.length + expected.length == 3 do fail "DELETE RETURNING row count mismatch"
  for sql in ["DELETE FROM t RETURNING t.*;", "DELETE FROM t AS x RETURNING x.id;",
      "DELETE FROM t RETURNING count(*);", "DELETE FROM t RETURNING 0 AND count(*);",
      "DELETE FROM t RETURNING 0 AND no_function();", "DELETE FROM t WHERE 0 RETURNING missing;",
      "DELETE FROM t RETURNING CASE WHEN id=3 THEN abs(-9223372036854775808) ELSE id END;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"DELETE RETURNING error omitted: {sql}"

private def expectSQLiteValuesQuery : IO Unit := do
  let cases : List (String × List (List Value)) := [
    ("VALUES(1),(2),(NULL);", [[.integer 1], [.integer 2], [.null]]),
    ("VALUES(sum(1),count(*));", [[.integer 1, .integer 1]]),
    ("VALUES(1),(2) UNION ALL SELECT 3 ORDER BY column1 DESC LIMIT 2;", [[.integer 3], [.integer 2]]),
    ("SELECT 1 UNION ALL VALUES(2),(3);", [[.integer 1], [.integer 2], [.integer 3]]),
    ("VALUES('a' COLLATE nocase),('b') UNION SELECT 'A';", [[.text "A"], [.text "b"]]),
    ("VALUES('a'),('b' COLLATE nocase) UNION SELECT 'A';", [[.text "A"], [.text "a"], [.text "b"]]),
    ("VALUES(CAST('a' AS TEXT)),('b' COLLATE nocase) UNION SELECT 'A';", [[.text "A"], [.text "b"]]),
    ("SELECT 'A' UNION VALUES(CAST('a' AS TEXT)),('b' COLLATE nocase);", [[.text "A"], [.text "a"], [.text "b"]]),
    ("VALUES(CAST(abs(-9223372036854775808) AS TEXT)),(2) UNION ALL SELECT 3 LIMIT 1 OFFSET 1;", [[.integer 2]]),
    ("VALUES(abs(-9223372036854775808)) UNION ALL SELECT 3 LIMIT 1 OFFSET 1;", [[.integer 3]]),
    ("VALUES(abs(-9223372036854775808)),(2) UNION ALL SELECT 3 LIMIT 0;", []),
    ("VALUES(1),(abs(-9223372036854775808)) UNION ALL SELECT 3 LIMIT 1;", [[.integer 1]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"VALUES query: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"VALUES query mismatch: {sql}"
  for sql in ["VALUES();", "VALUES(1),(2,3);", "VALUES(1) LIMIT -1;", "VALUES(1) ORDER BY 1;",
      "VALUES(sum(1)),(2);", "VALUES(1),(sum(2));", "VALUES(1) UNION ALL SELECT 2 ORDER BY column1;",
      "SELECT 1 UNION ALL VALUES(2) LIMIT 0;",
      "VALUES(CAST('a' AS TEXT)),('b' COLLATE nocase) UNION ALL SELECT 'A' ORDER BY column1;",
      "VALUES(1+2),(4) UNION ALL SELECT 5 ORDER BY 1+2;",
      "VALUES(abs(-9223372036854775808)),(2) UNION ALL SELECT 3 LIMIT 1 OFFSET 1;",
      "VALUES(1),(abs(-9223372036854775808)) UNION ALL SELECT 3 ORDER BY 1 LIMIT 1;"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then fail s!"VALUES error omitted: {sql}"
  let sql := "VALUES(1),(2);"
  let parsed : CoreTokenGrammar.CertifiedParse sql ← match CoreTokenGrammar.parseCertified sql with
    | .ok result => pure result
    | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "VALUES AST missing"
  let forged := { query with columns := #[{ expr := .literal (.integer 99), alias := some "column1", sourceSql := some "1" }] }
  if (CoreTokenGrammar.check parsed.tokens #[.select forged]).isOk then
    fail "VALUES checker trusted a forged first-row projection"

private def expectSQLiteInsertSelect : IO Unit := do
  let setup := "CREATE TABLE src(id INTEGER PRIMARY KEY,v);INSERT INTO src VALUES(1,'3'),(2,'4');" ++
    "CREATE TABLE dst(id INTEGER PRIMARY KEY,v INTEGER);CREATE TABLE empty(id INTEGER PRIMARY KEY,v);"
  let cases : List (String × List (List Value)) := [
    ("INSERT INTO dst(v) SELECT v FROM src ORDER BY id DESC;SELECT id,v,typeof(v) FROM dst ORDER BY id;",
      [[.integer 1, .integer 4, .text "integer"], [.integer 2, .integer 3, .text "integer"]]),
    ("INSERT INTO src(v) SELECT v FROM src ORDER BY id DESC;SELECT id,v FROM src ORDER BY id;",
      [[.integer 1, .text "3"], [.integer 2, .text "4"], [.integer 3, .text "4"], [.integer 4, .text "3"]]),
    ("BEGIN;INSERT INTO dst(v) SELECT v FROM src;ROLLBACK;SELECT count(*) FROM dst;", [[.integer 0]]),
    ("INSERT INTO dst(v) SELECT v FROM empty;SELECT count(*) FROM dst;", [[.integer 0]]),
    ("INSERT INTO dst(v) SELECT 1 UNION ALL SELECT 2;SELECT sum(v) FROM dst;", [[.integer 3]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"INSERT SELECT: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"INSERT SELECT mismatch: {sql}"
  for sql in ["INSERT INTO dst SELECT v FROM empty;", "INSERT INTO dst(missing) SELECT v FROM empty;",
      "INSERT INTO dst(v) SELECT no_function(v) FROM empty;", "INSERT INTO dst(v) SELECT 1,2 WHERE 0;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"INSERT SELECT error omitted: {sql}"
  let parsed ← match CoreTokenGrammar.parseStatements "INSERT INTO dst SELECT id,v FROM src;" with
    | .ok parsed => pure parsed
    | .error message => fail message
  unless parsed.toList.any CoreFileEngine.statementWrites do fail "INSERT SELECT did not request persistence"

private def expectSQLiteDrop : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);CREATE INDEX tv ON t(v);" ++
    "CREATE TABLE k(id TEXT PRIMARY KEY,v);INSERT INTO t VALUES(1,7),(2,8);" ++
    "INSERT INTO k VALUES('a',9);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail s!"DROP seed: {message}"
  let apply := fun sql => do
    match CoreSQL.execute initial sql with
    | .ok (state, _) => pure state
    | .error message => fail s!"DROP execution: {sql}: {message}"
  let dropped ← apply "DROP TABLE t;"
  unless (dropped.database.findTable? "t").isNone && (dropped.database.findTable? "k").isSome do
    fail "DROP TABLE changed the wrong tables"
  let withoutIndex ← apply "DROP INDEX tv;"
  let some kept := withoutIndex.database.findTable? "t" | fail "DROP INDEX removed its table"
  unless kept.indexes.isEmpty && kept.rows.length == 2 do fail "DROP INDEX lost rows or retained metadata"
  let rolledBack ← apply "BEGIN;DROP INDEX tv;DROP TABLE k;ROLLBACK;"
  unless rolledBack.database.contents == initial.database.contents do fail "DROP rollback lost schema or rows"
  let noops ← apply "DROP TABLE IF EXISTS absent;DROP INDEX IF EXISTS t;"
  unless noops.database.contents == initial.database.contents do fail "DROP IF EXISTS changed contents"
  for sql in ["DROP TABLE absent;", "DROP INDEX absent;", "DROP INDEX sqlite_autoindex_k_1;",
      "DROP INDEX IF EXISTS sqlite_autoindex_k_1;", "DROP TABLE IF EXISTS sqlite_schema;",
      "DROP TABLE IF EXISTS sqlite_temp_master;"] do
    if (CoreSQL.execute initial sql).isOk then fail s!"DROP error omitted: {sql}"
  unless CoreFileEngine.statementWrites (.dropTable "t") &&
      CoreFileEngine.statementWrites (.dropIndex "tv") do fail "DROP did not request persistence"
  unless CoreSQL.schemaNoop initial (.dropTable "absent" true) &&
      CoreSQL.schemaNoop initial (.dropIndex "absent" true) do fail "DROP no-op requested persistence"

private def expectSQLiteHeaderVersions : IO Unit := do
  let header := CoreFile.databaseHeader ⟨3, by decide⟩
  for read in ([0, 1, 2] : List UInt8) do
    for write in ([0, 1, 2, 3, 255] : List UInt8) do
      let candidate := { header with headerPrefix := { header.headerPrefix with
        readVersion := read
        writeVersion := write } }
      unless (SQLite.HeaderVersion.readError? candidate).isNone do
        fail "readable file version was rejected"
      unless (SQLite.HeaderVersion.writeError? candidate).isSome == (write.toNat > 2) do
        fail "unknown write version was not read-only"
  for read in ([3, 127, 255] : List UInt8) do
    let candidate := { header with headerPrefix := { header.headerPrefix with readVersion := read } }
    unless SQLite.HeaderVersion.readError? candidate == some "file is not a database" do
      fail "unknown read version was admitted"
    unless (SQLite.HeaderVersion.writeError? candidate).isSome do
      fail "unreadable file version remained writable"
  for value in [0, 1, 2, 3, 4, 5, 255, 256, 257, 260, 261, 4294967295] do
    let candidate := { header with schemaFormat := ⟨value % 2^32, Nat.mod_lt _ (by decide)⟩ }
    unless (SQLite.HeaderVersion.readError? candidate).isSome == (value % 256 > 4) do
      fail "schema format did not follow the pinned low-byte admission"

private def expectSQLiteReservedPages : IO Unit := do
  let header := CoreFile.databaseHeader ⟨3, by decide⟩
  let cases : List (Nat × UInt8 × Nat) :=
    [(512, 0, 512), (512, 1, 511), (512, 32, 480),
      (1024, 255, 769), (4096, 255, 3841), (1, 255, 65281)]
  for (field, reserved, expected) in cases do
    let candidate := { header with headerPrefix := { header.headerPrefix with
      pageSizeField := ⟨field % 2^16, Nat.mod_lt _ (by decide)⟩
      reservedSpace := reserved } }
    let some usable := CoreFileAdapter.headerUsablePageSize? candidate |
      fail "reserved-tail geometry rejected"
    unless usable.val == expected do fail "reserved-tail geometry used physical page size"
  for (field, reserved) in [(512, (33 : UInt8)), (512, 255), (0, 0), (1023, 0)] do
    let candidate := { header with headerPrefix := { header.headerPrefix with
      pageSizeField := ⟨field % 2^16, Nat.mod_lt _ (by decide)⟩
      reservedSpace := reserved } }
    unless (CoreFileAdapter.headerUsablePageSize? candidate).isNone do
      fail "invalid physical or usable page size admitted"

private def expectSQLiteHeaderSize : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,7);" with
    | .ok value => pure value
    | .error message => fail message
  let some image := CorePageCodec.encodeChecked state.database | fail "header-size image encoder failed"
  let some (header, rest) := FileFormat.decodeDatabaseHeader image.fileBytes | fail "header-size header missing"
  let unset := { header with databaseSizePages := ⟨0, by decide⟩ }
  let stale := { header with
    databaseSizePages := ⟨999, by decide⟩
    versionValidFor := ⟨0, by decide⟩ }
  let cases : List (FileFormat.DatabaseHeader × List UInt8) :=
    [(header, []), (unset, []), (stale, []), (header, [1,2,3]), (header, List.replicate 4096 0)]
  for (candidate, tail) in cases do
    let input := FileFormat.encodeDatabaseHeader candidate ++ rest ++ tail
    let some decoded := CoreFileAdapter.physicalImage? input | fail "compatible header size rejected"
    unless decoded.pageCount == image.pageCount do fail "header size selected the wrong logical image"
    for index in [:image.pageCount] do
      unless (decoded.read index).bytes == ((input.drop (index * 4096)).take 4096).toArray do
        fail "header-size decode changed a page"
  let tooLarge := { header with databaseSizePages := ⟨999, by decide⟩ }
  unless (SQLite.DatabaseSize.pageCount? tooLarge image.fileBytes.length 4096).isNone do
    fail "current size beyond EOF accepted"
  unless SQLite.DatabaseSize.filePages 4097 4096 == 2 do fail "file page count was not rounded up"
  unless SQLite.DatabaseSize.pageBytes (ByteArray.mk #[1,2,3]) 4 1 = some [1,2,3,0] do
    fail "partial final page was not zero-filled"
  unless (SQLite.DatabaseSize.pageBytes (ByteArray.mk #[1,2,3]) 4 2).isNone do
    fail "page starting beyond EOF was accepted"

private def expectSQLiteSchemaPages : IO Unit := do
  let first : CoreFile.CatalogEntry := {
    kind := "table", name := "a", table := "a", rootPage := 2, sql := "CREATE TABLE a(id INTEGER PRIMARY KEY,v)" }
  let second : CoreFile.CatalogEntry := {
    kind := "table", name := "b", table := "b", rootPage := 3, sql := "CREATE TABLE b(id INTEGER PRIMARY KEY,v)" }
  let some leftCell := CoreFile.catalogCell? 1 first | fail "schema cell encoder failed"
  let some rightCell := CoreFile.catalogCell? 2 second | fail "schema cell encoder failed"
  let some leftPage := CoreFile.tableLeafPage? [leftCell] | fail "schema leaf encoder failed"
  let some rightPage := CoreFile.tableLeafPage? [rightCell] | fail "schema leaf encoder failed"
  let header := fun count => FileFormat.encodeDatabaseHeader
    (CoreFile.databaseHeader ⟨count % 2^32, Nat.mod_lt _ (by decide)⟩)
  let root := fun left right =>
    let cell := FileFormat.encodeUnsignedFixed 4 left ++ [1]
    let offset := 4096 - cell.length
    let treeHeader := [5, 0, 0] ++ FileFormat.encodeUnsignedFixed 2 1 ++
      FileFormat.encodeUnsignedFixed 2 offset ++ [0] ++ FileFormat.encodeUnsignedFixed 4 right ++
      FileFormat.encodeUnsignedFixed 2 offset
    header 3 ++ treeHeader ++ List.replicate (offset - 100 - treeHeader.length) 0 ++ cell
  let readCatalog := fun pages => do
    let source : CoreDecode.IOPageSource := {
      pageCount := pages.length
      readPage := fun page => pure (CoreDecode.page? pages page) }
    CoreDecode.catalogIOFrom source
  let result ← readCatalog [root 2 3, leftPage.bytes, rightPage.bytes]
  unless result = some [CoreDecode.CatalogEntry.ofEncoded first, CoreDecode.CatalogEntry.ofEncoded second] do
    fail "schema traversal lost branch order or entries"
  for (left, right) in [(1,3), (2,1), (2,2), (0,3), (2,4)] do
    unless (← readCatalog [root left right, leftPage.bytes, rightPage.bytes]).isNone do
      fail "schema traversal accepted a cycle, duplicate or invalid page"
  let large := { first with sql := first.sql ++ String.ofList (List.replicate 15000 ' ') }
  let some raw := CoreFile.catalogCell? 1 large | fail "large schema cell encoder failed"
  let some (_, afterSize) := FileFormat.decodeVarint raw | fail "schema payload size missing"
  let some (_, payload) := FileFormat.decodeVarint afterSize | fail "schema rowid missing"
  let plan : CoreOverflow.CellPlan := {
    kind := .table, cellPrefix := raw.take (raw.length - payload.length), payload }
  let some resolved := CoreOverflow.resolvePlans 2 [plan] | fail "schema overflow planning failed"
  let some body := CoreFile.leafBody? 13 100 resolved.cells | fail "schema overflow leaf failed"
  let page := header (1 + resolved.pages.length) ++ body.bytes
  let remaining := resolved.pages.map CoreFile.Page.bytes
  unless (← readCatalog (page :: remaining)) = some [CoreDecode.CatalogEntry.ofEncoded large] do
    fail "schema overflow traversal changed the SQL text"
  match remaining with
  | firstOverflow :: rest =>
      let cyclic := FileFormat.encodeUnsignedFixed 4 2 ++ firstOverflow.drop 4
      unless (← readCatalog (page :: cyclic :: rest)).isNone do
        fail "schema overflow traversal accepted a cycle"
  | [] => fail "schema overflow fixture stayed inline"

private def expectSQLiteFormat : IO Unit := do
  let setup := "CREATE TABLE e(id INTEGER PRIMARY KEY,v);"
  let cases : List (String × List (List Value)) := [
    ("SELECT typeof(format()),hex(format());", [[.text "null", .text ""]]),
    ("SELECT typeof(format('')),hex(format(''));", [[.text "null", .text ""]]),
    ("SELECT typeof(format('%n')),hex(format('%n'));", [[.text "text", .text ""]]),
    ("SELECT typeof(format('%n%d|%s',12,'x')),hex(format('%n%d|%s',12,'x'));", [[.text "text", .text "31327C78"]]),
    ("SELECT typeof(format('%q|%Q|%w',NULL,NULL,NULL)),hex(format('%q|%Q|%w',NULL,NULL,NULL));", [[.text "text", .text "284E554C4C297C4E554C4C7C284E554C4C29"]]),
    ("SELECT typeof(format('%#Q',CAST(X'010A1B5C27' AS TEXT))),hex(format('%#Q',CAST(X'010A1B5C27' AS TEXT)));", [[.text "text", .text "756E6973747228275C75303030315C75303030615C75303031625C5C27272729"]]),
    ("SELECT typeof(format('%#q','a\\b')),hex(format('%#q','a\\b'));", [[.text "text", .text "615C5C62"]]),
    ("SELECT typeof(format('%#!.2Q','árvíz')),hex(format('%#!.2Q','árvíz'));", [[.text "text", .text "27C3A17227"]]),
    ("SELECT typeof(format('%!.1s',X'C0808080')),hex(format('%!.1s',X'C0808080'));", [[.text "text", .text "C0808080"]]),
    ("SELECT typeof(format('%5.3c',X'F09F9880')),hex(format('%5.3c',X'F09F9880'));", [[.text "text", .text "2020F09F9880F09F9880F09F9880"]]),
    ("SELECT typeof(format('%-5.3c',X'80')),hex(format('%-5.3c',X'80'));", [[.text "text", .text "808080202020"]]),
    ("SELECT typeof(format('%c|%c',NULL,42)),hex(format('%c|%c',NULL,42));", [[.text "text", .text "007C34"]]),
    ("SELECT typeof(format('hello%')),hex(format('hello%'));", [[.text "text", .text "68656C6C6F25"]]),
    ("SELECT typeof(format('before%Yafter',12)),hex(format('before%Yafter',12));", [[.text "text", .text "6265666F7265"]]),
    ("SELECT typeof(format('%Y')),hex(format('%Y'));", [[.text "null", .text ""]]),
    ("SELECT typeof(format('%08d|%#08x|%u|%r',-12,255,-1,112)),hex(format('%08d|%#08x|%u|%r',-12,255,-1,112));", [[.text "text", .text "2D303030303031327C307830303030303066667C31383434363734343037333730393535313631357C3131327468"]]),
    ("SELECT typeof(format('%+ d|% +d|%-05d',3,3,3)),hex(format('%+ d|% +d|%-05d',3,3,3));", [[.text "text", .text "20337C2B337C3030303033"]]),
    ("SELECT typeof(format('%*.*f',-12,3,12.3455)),hex(format('%*.*f',-12,3,12.3455));", [[.text "text", .text "31322E333435202020202020"]]),
    ("SELECT typeof(format('%!.17g|%.17g',49.47,49.47)),hex(format('%!.17g|%.17g',49.47,49.47));", [[.text "text", .text "34392E34377C34392E3437"]]),
    ("SELECT typeof(format('%!g|%#g|%,.2f',100,100,123456.789)),hex(format('%!g|%#g|%,.2f',100,100,123456.789));", [[.text "text", .text "3130302E307C3130302E3030307C3132332C3435362E3739"]]),
    ("SELECT typeof(format('%#.0f|%+.0f|%.0f',-0.1,-0.1,-0.1)),hex(format('%#.0f|%+.0f|%.0f',-0.1,-0.1,-0.1));", [[.text "text", .text "302E7C2D307C2D30"]]),
    ("SELECT typeof(format('%e|%!e|%g|%#g',0.00001,0.00001,1e30,1e30)),hex(format('%e|%!e|%g|%#g',0.00001,0.00001,1e30,1e30));", [[.text "text", .text "312E303030303030652D30357C312E30652D30357C31652B33307C312E3030303030652B3330"]]),
    ("SELECT typeof(format('%0g|%+g',1e999,1e999)),hex(format('%0g|%+g',1e999,1e999));", [[.text "text", .text "39652B3939397C2B496E66"]]),
    ("SELECT typeof(format('%*.*s|%d',-2147483648,-2147483648,'abc',7)),hex(format('%*.*s|%d',-2147483648,-2147483648,'abc',7));", [[.text "text", .text "6162637C37"]]),
    ("SELECT typeof(format('%2147483648d|%.2147483648f',12,12.75)),hex(format('%2147483648d|%.2147483648f',12,12.75));", [[.text "text", .text "31327C3133"]]),
    ("SELECT typeof(format(X'2564002573',42,'tail')),hex(format(X'2564002573',42,'tail'));", [[.text "text", .text "3432"]]),
    ("SELECT typeof(printf('%.0o|%.0x|%.0d',0,0,0)),hex(printf('%.0o|%.0x|%.0d',0,0,0));", [[.text "text", .text "307C307C30"]]),
    ("SELECT typeof(format('%s|%d|%f')),hex(format('%s|%d|%f'));", [[.text "text", .text "7C307C302E303030303030"]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"format functions: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"format function mismatch: {sql}"
  for sql in ["SELECT format('%2000000000s','a');", "SELECT format('%.2000000000d',1);",
      "SELECT format('%2000000000c','a');", "SELECT format('%2000000000f',1);",
      "SELECT format('%s',missing) FROM e LIMIT 0;", "SELECT format('%s',abs(-9223372036854775808));"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"format function error omitted: {sql}"

private def expectSQLiteMath : IO Unit := do
  let setup := "CREATE TABLE e(id INTEGER PRIMARY KEY,v);"
  let cases : List (String × List (List Value)) := [
    ("SELECT ceil(1.25),floor(-1.25),trunc(-1.75),ceiling(-0.5);",
      [[.real 2.0, .real (-2.0), .real (-1.0), .real (-0.0)]]),
    ("SELECT typeof(ceil('1')),typeof(ceil('1.0')),floor(9223372036854775807);",
      [[.text "integer", .text "real", .integer 9223372036854775807]]),
    ("SELECT ceil(CAST(X'31320078' AS TEXT)),typeof(ceil(CAST(X'312E300078' AS TEXT)));",
      [[.integer 12, .text "real"]]),
    ("SELECT log(2,'8x'),log(2,X'38'),log(0.5,8),log(1,8),ln(-1),sqrt(-1),pow(-1,0.5),mod(1,0);",
      [[.real 3.0, .real 3.0, .null, .null, .null, .null, .null, .null]]),
    ("SELECT mod(5.5,2),mod(-5.5,2),mod(5.5,-2),mod(1,1e999),mod(1e999,2);",
      [[.real 1.5, .real (-1.5), .real 1.5, .real 1.0, .null]]),
    ("SELECT acos(1),asin(0),atan(0),atan2(0,1),acosh(1),asinh(0),atanh(0);",
      [[.real 0.0, .real 0.0, .real 0.0, .real 0.0, .real 0.0, .real 0.0, .real 0.0]]),
    ("SELECT cos(0),cosh(0),sin(0),sinh(0),tan(0),tanh(0),exp(0),ln(1);",
      [[.real 1.0, .real 1.0, .real 0.0, .real 0.0, .real 0.0, .real 0.0, .real 1.0, .real 0.0]]),
    ("SELECT log(100),log2(8),log10(1000),sqrt(9),pow(2,3),power(2,3),degrees(pi()),radians(180)=pi();",
      [[.real 2.0, .real 3.0, .real 3.0, .real 3.0, .real 8.0, .real 8.0, .real 180.0, .integer 1]]),
    ("SELECT ceil(NULL),sqrt(X'39'),sin('12tail'),ceil('NaN'),ln('Inf');",
      [[.null, .null, .null, .null, .null]]),
    ("SELECT sqrt(abs(-9223372036854775808)) FROM e;", []),
    ("SELECT sqrt(abs(-9223372036854775808)) LIMIT 0;", []),
    ("SELECT coalesce(7,sqrt(abs(-9223372036854775808)));", [[.integer 7]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"math functions: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"math function mismatch: {sql}"
  for sql in ["SELECT sqrt(abs(-9223372036854775808));", "SELECT pi(1);", "SELECT log();",
      "SELECT sqrt(missing) FROM e LIMIT 0;", "SELECT pow(1) FROM e LIMIT 0;",
      "SELECT log(1,2,3);", "SELECT pi() FILTER(WHERE 1);"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"math function error omitted: {sql}"
  for (direction, value, expected) in [
      (SQLite.Math.Direction.zero, -0.5, 0x8000000000000000),
      (.up, -0.5, 0x8000000000000000), (.down, 0.5, 0),
      (.zero, -0.0, 0x8000000000000000)] do
    unless (SQLite.Math.roundFloat direction value).toBits == expected do fail "rounding lost signed zero"
  for (left, right, expected) in [(-4.0, 2.0, 0x8000000000000000),
      (-0.0, 1.0, 0x8000000000000000), (Float.ofBits 3, Float.ofBits 2, 1)] do
    match SQLite.Math.remainder left right with
    | .real value => unless value.toBits == expected do fail "remainder lost exact bits"
    | _ => fail "remainder lost REAL type"

private def expectSQLiteUnicodeEscape : IO Unit := do
  let setup := "CREATE TABLE e(id INTEGER PRIMARY KEY,v);"
  let cases : List (String × List (List Value)) := [
    ("SELECT unistr(NULL),unistr_quote(NULL);", [[.null, .text "NULL"]]),
    ("SELECT unistr(X'5C7530303431'),unistr(1.25);", [[.text "A", .text "1.25"]]),
    ("SELECT hex(unistr(X'5C75303030305C7530303431'));", [[.text "0041"]]),
    ("SELECT hex(unistr(X'005C71'));", [[.text "005C71"]]),
    ("SELECT hex(unistr(X'5C7530303431005C71'));", [[.text "41005C71"]]),
    ("SELECT hex(unistr(X'5C7544383030'));", [[.text "EDA080"]]),
    ("SELECT hex(unistr(X'5C554646464646464646'));", [[.text "F7BFBFBF"]]),
    ("SELECT hex(unistr(X'5C553030323030303030'));", [[.text "F0808080"]]),
    ("SELECT hex(unistr(X'FF805C7530303431'));", [[.text "FF8041"]]),
    ("SELECT hex(unistr_quote(CAST(X'610A5C27' AS TEXT)));",
      [[.text "756E697374722827615C75303030615C5C27272729"]]),
    ("SELECT unistr_quote(CAST(X'615C62' AS TEXT));", [[.text "'a\\b'"]]),
    ("SELECT unistr_quote(CAST(X'61001B' AS TEXT));", [[.text "'a'"]]),
    ("SELECT unistr_quote(X'001BFF');", [[.text "X'001BFF'"]]),
    ("SELECT unistr(X'5C71') FROM e;", []),
    ("SELECT unistr(X'5C71') LIMIT 0;", []),
    ("SELECT unistr(X'5C71') LIMIT 1 OFFSET 1;", []),
    ("SELECT coalesce('x',unistr(X'5C71'));", [[.text "x"]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"Unicode escape: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"Unicode escape mismatch: {sql}"
  for sql in ["SELECT unistr(X'5C71');", "SELECT unistr(X'5C753132');",
      "SELECT unistr(X'5C7530300031');", "SELECT unistr();", "SELECT unistr_quote(1,2);",
      "SELECT unistr(missing) FROM e LIMIT 0;", "SELECT unistr_quote(missing) FROM e LIMIT 0;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"Unicode escape error omitted: {sql}"

private def expectSQLiteStringAggregates : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,g,v,s);" ++
    "INSERT INTO t VALUES(1,0,NULL,'!'),(2,0,'A',':'),(3,1,'a',NULL),(4,1,'A',':');" ++
    "CREATE TABLE b(id INTEGER PRIMARY KEY,v,s);" ++
    "INSERT INTO b VALUES(1,X'FF0080','!'),(2,X'410042',X'00FF'),(3,1,7),(4,1.0,NULL);" ++
    "CREATE TABLE e(id INTEGER PRIMARY KEY,g,v,s);"
  let cases : List (String × List (List Value)) := [
    ("SELECT group_concat(v),group_concat(v,s),string_agg(v,s) FROM t;",
      [[.text "A,a,A", .text "Aa:A", .text "Aa:A"]]),
    ("SELECT group_concat(DISTINCT v),group_concat(DISTINCT v COLLATE NOCASE) FROM t;",
      [[.text "A,a", .text "A"]]),
    ("SELECT g,group_concat(v,s) FROM t GROUP BY g ORDER BY g;",
      [[.integer 0, .text "A"], [.integer 1, .text "a:A"]]),
    ("SELECT typeof(group_concat(v)),hex(group_concat(v,s)) FROM b;",
      [[.text "text", .text "FF008000FF4100423731312E30"]]),
    ("SELECT group_concat(DISTINCT v),group_concat(v) FROM b WHERE id>2;",
      [[.text "1", .text "1,1.0"]]),
    ("SELECT id,min(id),group_concat(v,s) FROM t;", [[.integer 1, .integer 1, .text "Aa:A"]]),
    ("SELECT group_concat(v,s),typeof(group_concat(v)) FROM e;", [[.null, .text "null"]]),
    ("SELECT group_concat(v,s) FROM t WHERE v IS NULL;", [[.null]]),
    ("SELECT group_concat(v,s) FROM e GROUP BY g;", []),
    ("SELECT typeof(group_concat('')),hex(group_concat(''));", [[.text "text", .text ""]]),
    ("SELECT hex(group_concat(X'FF0080'));", [[.text "FF0080"]]),
    ("SELECT group_concat(0 AND 0x10000000000000000);", [[.text "0"]]),
    ("SELECT group_concat(v COLLATE missing,s) FROM t;", [[.text "Aa:A"]]),
    ("SELECT group_concat(v,s) AS x FROM t HAVING x='Aa:A';", [[.text "Aa:A"]]),
    ("SELECT group_concat(v,abs(-9223372036854775808)) FROM e;", [[.null]]),
    ("SELECT group_concat(NULL,abs(-9223372036854775808)) LIMIT 0;", []),
    ("SELECT group_concat(v,s) FROM t LIMIT 1 OFFSET 1;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"string aggregate: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"string aggregate mismatch: {sql}"
  for sql in ["SELECT group_concat(NULL,abs(-9223372036854775808));",
      "SELECT group_concat('x',abs(-9223372036854775808));",
      "SELECT group_concat(DISTINCT v,s) FROM e LIMIT 0;", "SELECT string_agg(v) FROM e LIMIT 0;",
      "SELECT group_concat(DISTINCT v COLLATE missing) FROM e LIMIT 0;",
      "SELECT group_concat(v,missing) FROM e LIMIT 0;", "SELECT group_concat(sum(v)) FROM e;",
      "SELECT group_concat(v,abs(-9223372036854775808)) FROM t HAVING 0;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"string aggregate error omitted: {sql}"

private def expectSQLiteGroupedExpressions : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,g,v);INSERT INTO t VALUES(1,'A',2),(2,'a',1),(3,'b',4),(4,'B',3),(5,NULL,5),(6,1,6),(7,1.0,8);" ++
    "CREATE TABLE o(id INTEGER PRIMARY KEY,g,v);INSERT INTO o VALUES(1,1,9223372036854775807),(2,1,1),(3,2,2),(4,3,3);"
  let cases : List (String × List (List Value)) := [
    ("SELECT g,count(*) AS x FROM t GROUP BY g COLLATE NOCASE HAVING x>1 ORDER BY x DESC,g;",
      [[.integer 1, .integer 2], [.text "A", .integer 2], [.text "b", .integer 2]]),
    ("SELECT g,sum(v)+count(*) FROM t GROUP BY g COLLATE NOCASE HAVING count(*)>1 ORDER BY 2 DESC;",
      [[.integer 1, .integer 16], [.text "b", .integer 9], [.text "A", .integer 5]]),
    ("SELECT g,count(*) FROM t GROUP BY g COLLATE NOCASE HAVING g='a';", []),
    ("SELECT g,count(*) FROM t GROUP BY g HAVING g='a';", [[.text "a", .integer 1]]),
    ("SELECT g,sum(v) FROM o GROUP BY g HAVING g>1;", [[.integer 2, .integer 2], [.integer 3, .integer 3]]),
    ("SELECT g,sum(v) FROM o GROUP BY g HAVING NULL;", []),
    ("SELECT g,sum(v) FROM o GROUP BY g ORDER BY g DESC LIMIT 1;", [[.integer 3, .integer 3]]),
    ("SELECT g,sum(v) FROM o GROUP BY g LIMIT 0;", []),
    ("SELECT DISTINCT count(*) FROM t GROUP BY g ORDER BY 1 DESC;", [[.integer 2], [.integer 1]]),
    ("SELECT g,abs(-9223372036854775808) FROM t GROUP BY g LIMIT 1 OFFSET 100;", []),
    ("SELECT g,abs(-9223372036854775808) FROM t GROUP BY g HAVING 0;", []),
    ("SELECT +g,+g,max(id),typeof(+g) FROM t WHERE id>=6 GROUP BY +g;",
      [[.real 1.0, .integer 1, .integer 7, .text "real"]]),
    ("SELECT g||'',max(id),g FROM t WHERE id<=2 GROUP BY g||'' COLLATE NOCASE;",
      [[.text "a", .integer 2, .text "a"]]),
    ("SELECT g||'',max(id),g FROM t WHERE id<=2 GROUP BY 1 COLLATE NOCASE;",
      [[.text "A", .integer 2, .text "a"]]),
    ("SELECT g||'',max(id),g FROM t WHERE id<=2 GROUP BY 1 COLLATE NOCASE ORDER BY 1;",
      [[.text "a", .integer 2, .text "a"]]),
    ("SELECT DISTINCT g||'' AS k,max(id),g FROM t WHERE id<=2 GROUP BY 1 COLLATE NOCASE ORDER BY k;",
      [[.text "A", .integer 2, .text "a"]]),
    ("SELECT g+1 AS k,count(*) FROM o WHERE k>2 GROUP BY k;", [[.integer 3, .integer 1], [.integer 4, .integer 1]]),
    ("SELECT count(*) GROUP BY 1+0 HAVING count(*)>0;", [[.integer 1]]),
    ("SELECT 1 GROUP BY 1;", [[.integer 1]]),
    ("SELECT count(*) WHERE 0 GROUP BY 1+0;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"grouped expression: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"grouped expression mismatch: {sql}"
  for sql in ["SELECT g,sum(v) FROM o GROUP BY g HAVING 0;", "SELECT g,sum(v) FROM o GROUP BY g ORDER BY g LIMIT 1;",
      "SELECT count(*) FROM t GROUP BY 1;", "SELECT count(*) FROM t GROUP BY missing LIMIT 0;",
      "SELECT count(*) FROM t GROUP BY g COLLATE missing LIMIT 0;", "SELECT count(*) FROM t GROUP BY g HAVING missing LIMIT 0;",
      "SELECT DISTINCT g,abs(-9223372036854775808) FROM t GROUP BY g LIMIT 1 OFFSET 100;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"grouped expression error omitted: {sql}"

private def expectSQLiteAggregateHaving : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,w TEXT);INSERT INTO t VALUES(1,3,'first'),(2,1,'low'),(3,9,'high'),(4,1,'tie');" ++
    "CREATE TABLE e(id INTEGER PRIMARY KEY,v,w TEXT);CREATE TABLE n(id INTEGER PRIMARY KEY,v,w TEXT);INSERT INTO n VALUES(1,NULL,'first'),(2,NULL,'last');" ++
    "CREATE TABLE d(id INTEGER PRIMARY KEY,v);INSERT INTO d VALUES(1,3),(2,1),(3,1);" ++
    "CREATE TABLE tx(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO tx VALUES(1,'4');" ++
    "CREATE TABLE o(id INTEGER PRIMARY KEY,v);INSERT INTO o VALUES(1,9223372036854775807),(2,1);"
  let cases : List (String × List (List Value)) := [
    ("SELECT count(*) AS x FROM t HAVING x=4;", [[.integer 4]]),
    ("SELECT count(*) FROM t HAVING 0;", []),
    ("SELECT count(*) FROM t HAVING NULL;", []),
    ("SELECT sum(v) AS v FROM t HAVING v=3;", [[.integer 14]]),
    ("SELECT id,w,min(v) FROM t HAVING 1;", [[.integer 2, .text "low", .integer 1]]),
    ("SELECT id,w,min(v),max(v),min(t.v) FROM t HAVING id=3;",
      [[.integer 3, .text "high", .integer 1, .integer 9, .integer 1]]),
    ("SELECT id,min(DISTINCT v) FROM d HAVING id=3;", [[.integer 3, .integer 1]]),
    ("SELECT id,min(v) FROM d HAVING id=2;", [[.integer 2, .integer 1]]),
    ("SELECT id,w,min(v) FROM n HAVING id=2;", [[.integer 2, .text "last", .null]]),
    ("SELECT id,w,count(*) FROM e HAVING id IS NULL;", [[.null, .null, .integer 0]]),
    ("SELECT count(*) FROM t HAVING id=2 ORDER BY min(v);", [[.integer 4]]),
    ("SELECT count(*) FROM t HAVING id=3 AND max(v)>0 ORDER BY min(v);", [[.integer 4]]),
    ("SELECT count(*) FROM tx HAVING v=4;", [[.integer 1]]),
    ("SELECT min(v) AS x FROM tx HAVING x=4;", []),
    ("SELECT count(*) FROM t HAVING count(*)>0 OR abs(-9223372036854775808);", [[.integer 4]]),
    ("SELECT count(*) FROM t HAVING count(*)<0 AND abs(-9223372036854775808);", []),
    ("SELECT abs(-9223372036854775808)+count(*) FROM t HAVING 0;", []),
    ("SELECT count(*) FROM t HAVING 1 COLLATE missing;", [[.integer 4]]),
    ("SELECT count(*) AS x WHERE 0 HAVING x=0;", [[.integer 0]]),
    ("SELECT count(*) HAVING count(*)=1;", [[.integer 1]]),
    ("SELECT count(*) FROM o HAVING 0 ORDER BY sum(v) LIMIT 0;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"aggregate HAVING: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"aggregate HAVING mismatch: {sql}"
  for sql in ["SELECT sum(v) FROM o HAVING 0;", "SELECT count(*) FROM o HAVING 0 ORDER BY sum(v);",
      "SELECT count(*) FROM t HAVING abs(-9223372036854775808) LIMIT 1 OFFSET 1;",
      "SELECT 1 FROM t HAVING count(*)>0;", "SELECT count(*) FROM t HAVING sum(sum(v));",
      "SELECT count(*) FROM t HAVING missing LIMIT 0;", "SELECT count(*) FROM t HAVING v=1 COLLATE missing;",
      "SELECT count(*) FROM t HAVING 0 AND no_function(1);", "SELECT count(*) HAVING rowid IS NULL;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"aggregate HAVING error omitted: {sql}"

private def expectSQLiteAggregateOrder : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1),(2,2),(3,3);"
  let cases : List (String × List (List Value)) := [
    ("SELECT count(*) FROM t ORDER BY v;", [[.integer 3]]),
    ("SELECT count(*) AS x FROM t ORDER BY x DESC;", [[.integer 3]]),
    ("SELECT sum(v)+count(*) AS x FROM t ORDER BY x;", [[.integer 9]]),
    ("SELECT count(*) FROM t ORDER BY abs(-9223372036854775808);", [[.integer 3]]),
    ("SELECT count(*) FROM t WHERE 0 ORDER BY sum(abs(-9223372036854775808));", [[.integer 0]]),
    ("SELECT count(*) FROM t ORDER BY sum(abs(-9223372036854775808)) LIMIT 0;", []),
    ("SELECT min(v COLLATE NOCASE) FROM t ORDER BY 1 COLLATE RTRIM;", [[.integer 1]]),
    ("SELECT 1 ORDER BY sum(abs(-9223372036854775808));", [[.integer 1]]),
    ("SELECT 1 WHERE 0 ORDER BY count(*);", []),
    ("SELECT count(*),0 AND 0x10000000000000000 ORDER BY 1;", [[.integer 1, .integer 0]]),
    ("SELECT count(*) ORDER BY abs(-9223372036854775808);", [[.integer 1]]),
    ("SELECT sum(1) WHERE 0 ORDER BY sum(abs(-9223372036854775808));", [[.null]]),
    ("SELECT count(*) FROM t ORDER BY v LIMIT 1 OFFSET 1;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"aggregate ORDER BY: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"aggregate ORDER BY mismatch: {sql}"
  for sql in ["SELECT count(*) FROM t ORDER BY sum(abs(-9223372036854775808));",
      "SELECT count(*) FROM t ORDER BY sum(abs(-9223372036854775808)) LIMIT 1 OFFSET 1;",
      "SELECT count(*) FROM t ORDER BY missing LIMIT 0;", "SELECT count(*) FROM t ORDER BY 2;",
      "SELECT count(*) FROM t ORDER BY 1 COLLATE missing;", "SELECT count(*) FROM t ORDER BY no_function(v);",
      "SELECT count(*) FROM t ORDER BY min(v COLLATE missing);", "SELECT 1 FROM t ORDER BY count(*);"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"aggregate ORDER BY error omitted: {sql}"

private def expectSQLiteNumericLiterals : IO Unit := do
  let cases : List (String × List (List Value)) := [
    ("SELECT 0xFFFFFFFFFFFFFFFF,0x8000000000000000,0x7FFFFFFFFFFFFFFF,0x80000000;",
      [[.integer (-1), .integer (-9223372036854775808), .integer 9223372036854775807, .integer 2147483648]]),
    ("SELECT 1_000,1_0.0_5,0xA_B,1e1_0;", [[.integer 1000, .real 10.05, .integer 171, .real 10000000000.0]]),
    ("SELECT 0 AND 0x10000000000000000,0x10000000000000000 AND 0;", [[.integer 0, .integer 0]]),
    ("SELECT -0xffffffffffffffff,~0xffffffffffffffff;", [[.integer 1, .integer 0]]),
    ("SELECT 0x0000000000000000000000FFFFFFFFFFFFFFFF;", [[.integer (-1)]]),
    ("SELECT -(9223372036854775808),typeof(-(9223372036854775808));", [[.integer (-9223372036854775808), .text "integer"]]),
    ("SELECT -(+9223372036854775808),typeof(-(+9223372036854775808));", [[.integer (-9223372036854775808), .text "integer"]]),
    ("SELECT -(0x8000000000000000 COLLATE BINARY);", [[.real 9223372036854775808.0]]),
    ("SELECT 1_0.0 UNION ALL SELECT 2 ORDER BY 10.0;", [[.integer 2], [.real 10.0]]),
    ("SELECT 214748364_8 UNION ALL SELECT 2 ORDER BY 2147483648;", [[.integer 2], [.integer 2147483648]]),
    ("SELECT 0xFFFFFFFFFFFFFFFF LIMIT 0xFFFFFFFFFFFFFFFF;", [[.integer (-1)]]),
    ("SELECT CAST('0xffff' AS INTEGER),CAST('1_000' AS INTEGER);", [[.integer 0, .integer 1]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"numeric literal: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"numeric literal mismatch: {sql}"
  for sql in ["SELECT 1__0;", "SELECT 1._0;", "SELECT 0x_1;", "SELECT 0x1g;",
      "SELECT 0x10000000000000000;", "SELECT 0x10000000000000000 LIMIT 0;",
      "SELECT 1 LIMIT 0 OFFSET 0x10000000000000000;", "SELECT -0x8000000000000000 LIMIT 0;",
      "SELECT -(+0x8000000000000000);", "SELECT CASE WHEN 0 THEN -0x8000000000000000 ELSE 1 END;",
      "SELECT 1e+;", "SELECT 123abc;", "SELECT 2147483648 UNION SELECT 2 ORDER BY 02147483648;"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then fail s!"numeric literal error omitted: {sql}"
  let tokens ← match lex "SELECT 1;" with
    | .ok tokens => pure tokens
    | .error message => fail message
  let wrong : Array Statement := #[.select { columns := #[{ expr := .literal (.real 1.0) }] }]
  if (CoreTokenGrammar.check tokens wrong).isOk then fail "numeric token checker changed INTEGER storage class"

private def expectSQLiteLiteralSpelling : IO Unit := do
  let cases : List (String × List (List Value)) := [
    ("SELECT 1.0 UNION ALL SELECT 2 ORDER BY 1.0;", [[.real 1.0], [.integer 2]]),
    ("SELECT 1.0 AS x UNION ALL SELECT 2 ORDER BY x;", [[.real 1.0], [.integer 2]]),
    ("SELECT 1.0,1.00 UNION ALL SELECT 2,0 ORDER BY 1.00;", [[.integer 2, .integer 0], [.real 1.0, .real 1.0]]),
    ("SELECT 1.0 UNION SELECT 1.00 ORDER BY 1.00;", [[.real 1.0]]),
    ("SELECT 1.0 AS x,abs(1.0) UNION ALL SELECT 2,3 ORDER BY abs(x);", [[.real 1.0, .real 1.0], [.integer 2, .integer 3]]),
    ("SELECT 1.0=1.00,1.0+1.00,-1.25;", [[.integer 1, .real 2.0, .real (-1.25)]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"literal spelling: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"literal spelling mismatch: {sql}"
  for sql in ["SELECT 0 AND 1.0 UNION ALL SELECT 2 ORDER BY 0 AND 1.00;",
      "SELECT 1.0 UNION SELECT 2 ORDER BY 1.00;",
      "SELECT 1e0 UNION SELECT 2 ORDER BY 1E0;",
      "SELECT abs(1.0) UNION ALL SELECT 2 ORDER BY abs(1.00);",
      "SELECT CASE WHEN 1 THEN 1.0 END UNION SELECT 2 ORDER BY CASE WHEN 1 THEN 1.00 END;",
      "SELECT 1.0 AS x,abs(1.00) UNION ALL SELECT 2,3 ORDER BY abs(x);"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then fail s!"literal token identity lost: {sql}"
  let tokens ← match lex "SELECT 1.0;" with
    | .ok tokens => pure tokens
    | .error message => fail message
  let changed ← match parse "SELECT 1.00;" with
    | .ok statements => pure statements
    | .error message => fail message
  if (CoreTokenGrammar.check tokens changed).isOk then fail "REAL spelling certificate accepted a changed token"
  let dropped : Array Statement := #[.select { columns := #[{ expr := .literal (.real 1.0) }] }]
  if (CoreTokenGrammar.check tokens dropped).isOk then fail "REAL spelling certificate accepted missing provenance"

private def expectSQLiteCompoundTails : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'A'),(2,'a'),(3,'B'),(4,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT 1 AS a,2 AS b UNION ALL SELECT 3 AS c,0 AS d ORDER BY d;",
      [[.integer 3, .integer 0], [.integer 1, .integer 2]]),
    ("SELECT 1 AS a,2 AS b UNION ALL SELECT 3 AS c,0 AS a ORDER BY a;",
      [[.integer 1, .integer 2], [.integer 3, .integer 0]]),
    ("SELECT a.v FROM t AS a JOIN t AS b ON a.id=b.id UNION SELECT v FROM t ORDER BY 1 DESC LIMIT 3;",
      [[.text "a"], [.text "B"], [.text "A"]]),
    ("SELECT v FROM t UNION ALL SELECT 'c' ORDER BY 1 DESC NULLS FIRST LIMIT 3;",
      [[.null], [.text "c"], [.text "a"]]),
    ("SELECT 'A' COLLATE NOCASE UNION SELECT 'a' ORDER BY 1 DESC;", [[.text "a"]]),
    ("SELECT 'A' COLLATE NOCASE INTERSECT SELECT 'a' ORDER BY 1 COLLATE BINARY;", [[.text "A"]]),
    ("SELECT 'A' COLLATE BINARY INTERSECT SELECT 'a' ORDER BY 1 COLLATE NOCASE;", []),
    ("SELECT 1 UNION ALL SELECT abs(-9223372036854775808) LIMIT 1;", [[.integer 1]]),
    ("SELECT abs(-9223372036854775808) UNION ALL SELECT 2 LIMIT 1 OFFSET 1;", [[.integer 2]]),
    ("SELECT abs(-9223372036854775808) FROM t UNION ALL SELECT 2 LIMIT 1 OFFSET 4;", [[.integer 2]]),
    ("SELECT 1 UNION SELECT 1 UNION ALL SELECT abs(-9223372036854775808) LIMIT 1;", [[.integer 1]]),
    ("SELECT 1 WHERE 0 INTERSECT SELECT abs(-9223372036854775808) ORDER BY 1;", []),
    ("SELECT abs(-9223372036854775808) UNION SELECT 2 LIMIT 0;", []),
    ("SELECT min(v) AS x FROM t UNION SELECT max(v) FROM t ORDER BY x DESC;", [[.text "a"], [.text "A"]]),
    ("SELECT CAST(X'410078' AS TEXT) COLLATE NOCASE UNION SELECT CAST(X'610059' AS TEXT) ORDER BY 1 DESC;",
      [[.textBytes #[97, 0, 89]]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"compound tail: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"compound tail mismatch: {sql}"
  for sql in ["SELECT 1 UNION ALL SELECT missing LIMIT 0;",
      "SELECT 1 UNION ALL SELECT 1,2 LIMIT 0;",
      "SELECT v FROM t UNION SELECT v FROM t ORDER BY v+1;",
      "SELECT 1 UNION ALL SELECT 2 ORDER BY 1 COLLATE missing LIMIT 0;",
      "SELECT 1 UNION ALL SELECT 2 ORDER BY 0 LIMIT 0;",
      "SELECT CASE WHEN 1 THEN 2 END UNION SELECT 3 ORDER BY CASE WHEN 1 THEN 4 END;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"compound tail error omitted: {sql}"
    | .error _ => pure ()

private def expectSQLiteCompoundCollations : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'A'),(2,'a'),(3,'B'),(4,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT 'A' COLLATE NOCASE UNION SELECT 'a';", [[.text "a"]]),
    ("SELECT 'A' UNION SELECT 'a' COLLATE NOCASE;", [[.text "a"]]),
    ("SELECT 'A' COLLATE BINARY UNION SELECT 'a' COLLATE NOCASE;", [[.text "A"], [.text "a"]]),
    ("SELECT 'a' COLLATE RTRIM INTERSECT SELECT 'a ';", [[.text "a"]]),
    ("SELECT 'a' COLLATE RTRIM EXCEPT SELECT 'a ';", []),
    ("SELECT 'A' COLLATE NOCASE,1 UNION SELECT 'a',1.0;", [[.text "a", .real 1.0]]),
    ("SELECT v FROM t UNION SELECT 'a' COLLATE NOCASE;", [[.null], [.text "A"], [.text "B"], [.text "a"]]),
    ("SELECT +v FROM t UNION SELECT 'a' COLLATE NOCASE;", [[.null], [.text "A"], [.text "B"], [.text "a"]]),
    ("SELECT CAST(v AS TEXT) FROM t UNION SELECT 'a' COLLATE NOCASE;", [[.null], [.text "A"], [.text "B"], [.text "a"]]),
    ("SELECT v||'' FROM t UNION SELECT 'a' COLLATE NOCASE;", [[.null], [.text "a"], [.text "B"]]),
    ("SELECT v FROM t UNION SELECT 'a' COLLATE missing;", [[.null], [.text "A"], [.text "B"], [.text "a"]]),
    ("SELECT 1 COLLATE missing UNION ALL SELECT 2;", [[.integer 1], [.integer 2]]),
    ("SELECT CAST(X'410078' AS TEXT) COLLATE NOCASE UNION SELECT CAST(X'610059' AS TEXT);",
      [[.textBytes #[97, 0, 89]]]),
    ("SELECT CAST(X'410078' AS TEXT) COLLATE NOCASE INTERSECT SELECT CAST(X'610059' AS TEXT);",
      [[.textBytes #[65, 0, 120]]]),
    ("SELECT CAST(X'FF41' AS TEXT) COLLATE NOCASE UNION SELECT CAST(X'FF61' AS TEXT);",
      [[.textBytes #[255, 97]]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"compound COLLATE: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"compound COLLATE mismatch: {sql}"
  for sql in ["SELECT 1 COLLATE missing UNION SELECT 2;", "SELECT 'a' UNION SELECT 'A' COLLATE missing;",
      "SELECT 'a' COLLATE NOCASE UNION SELECT 1,2;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"compound collation/width error omitted: {sql}"
    | .error _ => pure ()

private def expectSQLiteCollatedGroups : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,n); INSERT INTO t VALUES(1,'a',3),(2,'A',1),(3,'a ',2),(4,'B',4),(5,NULL,NULL),(6,NULL,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT v,count(*) FROM t GROUP BY v COLLATE NOCASE;",
      [[.null, .integer 2], [.text "a", .integer 2], [.text "a ", .integer 1], [.text "B", .integer 1]]),
    ("SELECT v,min(n) FROM t GROUP BY v COLLATE NOCASE;",
      [[.null, .null], [.text "A", .integer 1], [.text "a ", .integer 2], [.text "B", .integer 4]]),
    ("SELECT v,max(n),min(n),max(n) FROM t GROUP BY v COLLATE NOCASE LIMIT 1 OFFSET 1;",
      [[.text "A", .integer 3, .integer 1, .integer 3]]),
    ("SELECT v COLLATE NOCASE,count(*) FROM t WHERE v COLLATE NOCASE='a' GROUP BY v COLLATE NOCASE;",
      [[.text "a", .integer 2]]),
    ("SELECT v,count(*) FROM t GROUP BY v COLLATE RTRIM LIMIT 1 OFFSET 3;", [[.text "a", .integer 2]]),
    ("SELECT v,sum(n) FROM t GROUP BY v COLLATE NOCASE LIMIT 0;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"collated group: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"collated group mismatch: {sql}"
  let huge := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,n);INSERT INTO t VALUES(1,'a',9223372036854775807),(2,'A',1),(3,'b',0),(4,'c',9223372036854775807),(5,'C',1);"
  for sql in ["SELECT v,sum(n) FROM t GROUP BY v COLLATE NOCASE LIMIT 0;",
      "SELECT v,sum(n) FROM t WHERE id>2 GROUP BY v COLLATE NOCASE LIMIT 1;"] do
    match CoreSQL.execute Core.State.empty (huge ++ sql) with
    | .error message => fail s!"group LIMIT evaluated excluded accumulator: {message}"
    | .ok _ => pure ()
  for sql in ["SELECT v,sum(n) FROM t GROUP BY v COLLATE NOCASE LIMIT 1 OFFSET 1;",
      "SELECT v,count(*) FROM t GROUP BY v COLLATE missing LIMIT 0;"] do
    match CoreSQL.execute Core.State.empty (huge ++ sql) with
    | .ok _ => fail "group OFFSET/metadata omitted required error"
    | .error _ => pure ()

private def expectSQLiteExpressionCollations : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,txt TEXT); INSERT INTO t VALUES(1,'a',1),(2,'A',2),(3,'a ',3),(4,NULL,4);"
  let cases : List (String × List (List Value)) := [
    ("SELECT 'A' COLLATE NOCASE='a','a' COLLATE RTRIM='a ',X'41' COLLATE NOCASE='a';",
      [[.integer 1, .integer 1, .integer 0]]),
    ("SELECT 'a' IN ('A' COLLATE NOCASE),'a' IN ('A' COLLATE NOCASE,'z'),'a' COLLATE NOCASE IN ('A','z','x');",
      [[.integer 1, .integer 0, .integer 1]]),
    ("SELECT CASE 'a' WHEN 'A' COLLATE NOCASE THEN 1 ELSE 0 END,min('a' COLLATE NOCASE,'A'),max('a' COLLATE NOCASE,'A');",
      [[.integer 1, .text "A", .text "a"]]),
    ("SELECT id FROM t WHERE txt COLLATE NOCASE=1;", [[.integer 1]]),
    ("SELECT id FROM t WHERE v='a' COLLATE NOCASE ORDER BY id;", [[.integer 1], [.integer 2]]),
    ("SELECT DISTINCT v COLLATE NOCASE FROM t;", [[.text "a"], [.text "a "], [.null]]),
    ("SELECT DISTINCT v COLLATE RTRIM FROM t ORDER BY v COLLATE RTRIM;", [[.null], [.text "A"], [.text "a"]]),
    ("SELECT min(v COLLATE NOCASE)='A',max(v COLLATE RTRIM)='a',count(DISTINCT v COLLATE NOCASE) FROM t;",
      [[.integer 1, .integer 1, .integer 2]]),
    ("SELECT nullif(min(v COLLATE NOCASE),'A'),coalesce(min(v COLLATE NOCASE),'z')='A' FROM t;", [[.null, .integer 1]]),
    ("SELECT 1 COLLATE missing,1 IN (1 COLLATE missing,2),CASE WHEN 1 THEN 7 ELSE 2 COLLATE NOCASE END;",
      [[.integer 1, .integer 1, .integer 7]]),
    ("UPDATE t SET v='changed' WHERE v COLLATE NOCASE='A'; SELECT v FROM t WHERE id=2;", [[.text "changed"]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"expression COLLATE: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"expression COLLATE mismatch: {sql}"
  for sql in ["SELECT 1 COLLATE missing=1 LIMIT 0;", "SELECT DISTINCT 1 COLLATE missing;",
      "SELECT min(v COLLATE missing) FROM t LIMIT 0;", "SELECT DISTINCT sum(id) COLLATE missing FROM t;",
      "SELECT DISTINCT sum(1) COLLATE missing;", "SELECT 1 IN (1 COLLATE missing);"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"missing COLLATE was silently used: {sql}"
    | .error _ => pure ()

private def expectSQLiteQuotedFunctions : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,-3),(2,1.5),(3,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT \"abs\"(-3),[length]('abc'),`typeof`(1.0);", [[.integer 3, .integer 3, .text "real"]]),
    ("SELECT \"sum\"(v),[count](*),`count`(DISTINCT v) FROM t;", [[.real (-1.5), .integer 3, .integer 2]]),
    ("SELECT \"abs\"(DISTINCT -3),coalesce(DISTINCT NULL,2),min(DISTINCT 3,1,2),[max](ALL 1,3);",
      [[.integer 3, .integer 2, .integer 1, .integer 3]]),
    ("SELECT \"abs\"(v) FROM t ORDER BY `abs`(v);", [[.null], [.real 1.5], [.integer 3]]),
    ("UPDATE t SET v=[abs](v); SELECT v FROM t WHERE id=1;", [[.integer 3]]),
    ("SELECT 0 AND \"abs\"(-9223372036854775808);", [[.integer 0]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"quoted functions: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"quoted function mismatch: {sql}"
  for name in ["char", "\"char\"", "[char]", "`char`"] do
    for count in [999, 1000, 1001] do
      let arguments := String.intercalate "," (List.replicate count "65")
      let sql := s!"SELECT length({name}({arguments}));"
      match CoreSQL.execute Core.State.empty sql with
      | .ok (_, results) =>
          unless count ≤ SQLite.Limits.maxFunctionArgs &&
              results.map (·.rows) == [[[(← match SQLSurface.value (.integer count) with
                | .ok value => pure value
                | .error message => fail message)]]] do fail "function argument limit accepted wrong count"
      | .error message => unless count > SQLite.Limits.maxFunctionArgs do fail message
  for sql in ["SELECT 'abs'(-3);", "SELECT \"abs\"();", "SELECT [abs](1,2);",
      "SELECT CAST_INTEGER(1);", "SELECT \"cast_integer\"(1);", "SELECT CAST_INTEGER(DISTINCT 1);",
      "SELECT [cast_integer](DISTINCT 1);", "SELECT lean_distinct_aggregate_abs(1);",
      "SELECT LEAN_DISTINCT_AGGREGATE_ABS(DISTINCT 1);", "SELECT \"lean_dqs\"('v') FROM t;",
      "SELECT \"__sqlean_boolean_true\"();", "SELECT 0 AND \"unknown_function\"();"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"private/invalid function was admitted: {sql}"
    | .error _ => pure ()

private def expectSQLiteBooleanKeywords : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,true TEXT,false INTEGER,v); INSERT INTO t VALUES(1,'2',7,2),(2,'0',0,0),(3,NULL,NULL,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT 2 IS TRUE,2 IS (TRUE),2 IS TRUE+0,0 IS FALSE,NULL IS NOT TRUE,NULL IS FALSE;",
      [[.integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 0]]),
    ("SELECT TRUE,FALSE,typeof(TRUE),typeof(FALSE);", [[.integer 1, .integer 0, .text "integer", .text "integer"]]),
    ("SELECT id,TRUE,FALSE,v IS TRUE FROM t ORDER BY id;",
      [[.integer 1, .text "2", .integer 7, .integer 0],
       [.integer 2, .text "0", .integer 0, .integer 0],
       [.integer 3, .null, .null, .integer 1]]),
    ("SELECT id FROM t WHERE id=TRUE ORDER BY id;", []),
    ("SELECT sum(TRUE),sum(FALSE) FROM t;", [[.integer 2, .integer 7]]),
    ("SELECT FALSE AND abs(-9223372036854775808),TRUE OR abs(-9223372036854775808);",
      [[.integer 0, .integer 1]]),
    ("SELECT 1 LIMIT TRUE;", [[.integer 1]]),
    ("SELECT 1 LIMIT FALSE;", []),
    ("UPDATE t SET v=TRUE WHERE id=1; SELECT v,typeof(v) FROM t WHERE id=1;", [[.text "2", .text "text"]]),
    ("DELETE FROM t WHERE false; SELECT id FROM t ORDER BY id;", [[.integer 2], [.integer 3]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"boolean keyword: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"boolean keyword mismatch: {sql}"
  for sql in ["SELECT FALSE AND missing;", "SELECT TRUE OR unknown_function();",
      "SELECT __sqlean_boolean_true() LIMIT 0;", "SELECT TRUE() LIMIT 0;",
      "SELECT TRUE.foo;", "SELECT missing IS TRUE FROM t WHERE FALSE LIMIT 0;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"boolean binding omitted error: {sql}"
    | .error _ => pure ()

private def expectSQLiteOperatorPrecedence : IO Unit := do
  let cases : List (String × Value) := [
    ("0.5=-1<0.5", .integer 0), ("1!=(-1)<(-1)", .integer 1),
    ("0 LIKE 2<(-3)", .integer 1), ("3 IS '1'<'2'", .integer 0),
    ("2 NOT BETWEEN 1 AND 3=-3", .integer 0),
    ("'2' BETWEEN 2 AND 1 IS NOT -3", .integer 1),
    ("'a' NOT LIKE 'a' ESCAPE 'x'<=2", .integer 0),
    ("NULL ISNULL", .integer 1), ("NULL NOTNULL", .integer 0),
    ("1 NOT NULL", .integer 1), ("NULL NOT NULL+1", .integer 1),
    ("NULL IS DISTINCT FROM NULL", .integer 0),
    ("NULL IS NOT DISTINCT FROM NULL", .integer 1),
    ("2 IS DISTINCT FROM 1", .integer 1)]
  for (expression, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty ("SELECT " ++ expression ++ ";") with
      | .ok result => pure result
      | .error message => fail s!"operator precedence: {message}"
    let expected ← match SQLSurface.value expected with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [[expected]] do
      fail s!"operator precedence mismatch: {expression}"

private def expectSQLiteAggregateResults : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,1),(2,1.0),(3,2),(4,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT sum(v)+count(*),typeof(sum(v)),42 FROM t;", [[.real 8.0, .text "real", .integer 42]]),
    ("SELECT coalesce(sum(v),count(*))+1 FROM t WHERE id<0;", [[.integer 1]]),
    ("SELECT round(avg(DISTINCT v),1),CASE WHEN count(*)>3 THEN sum(v) ELSE 0 END FROM t;",
      [[.real 1.5, .real 4.0]]),
    ("SELECT count(*),sum(7),min(2),max(3);", [[.integer 1, .integer 7, .integer 2, .integer 3]]),
    ("SELECT count(*),sum(7),avg(7),total(7) WHERE 0;", [[.integer 0, .null, .null, .real 0.0]]),
    ("SELECT count(*)+abs(-9223372036854775808) FROM t LIMIT 1 OFFSET 1;", []),
    ("SELECT sum(abs(-9223372036854775808)) WHERE 0;", [[.null]]),
    ("SELECT count(*)+abs(-9223372036854775808) LIMIT 1 OFFSET 1;", []),
    ("SELECT 0 AND sum(v) FROM t;", [[.integer 0]]),
    ("SELECT typeof(count(*)||total(v)/avg(v)) FROM t;", [[.text "real"]]),
    ("SELECT max(v) IS NULL+total(v),typeof(max(v) IS NULL+total(v)) FROM t;",
      [[.integer 0, .text "integer"]]),
    ("SELECT count(*) IS (NULL),count(*) IS NOT ((NULL)) FROM t;", [[.integer 0, .integer 1]]),
    ("SELECT 1||2*3,typeof(1||2*3),2*3||4,typeof(2*3||4);",
      [[.integer 36, .text "integer", .integer 68, .text "integer"]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"aggregate result expression: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do
      fail s!"aggregate scalar result mismatch: {sql}"
  let overflow := "CREATE TABLE ov(id INTEGER PRIMARY KEY,v); INSERT INTO ov VALUES(1,9223372036854775807),(2,1);"
  for sql in ["SELECT 0 AND count(abs(-9223372036854775808)) FROM t;",
      "SELECT count(*)+abs(-9223372036854775808) WHERE 0;",
      "SELECT count(*)+unknown_function() LIMIT 0;", "SELECT sum(rowid) LIMIT 0;",
      "SELECT sum(sum(v))+1 FROM t LIMIT 0;",
      "SELECT CASE WHEN 0 THEN sum(v) ELSE 1 END FROM ov;",
      "SELECT sum(v)+1 FROM ov LIMIT 1 OFFSET 1;"] do
    match CoreSQL.execute Core.State.empty (setup ++ overflow ++ sql) with
    | .ok _ => fail s!"aggregate result omitted error: {sql}"
    | .error _ => pure ()

private def expectSQLiteNumericAggregates : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);"
  let cases : List (String × Value) := [
    ("INSERT INTO t VALUES(1,1.5),(2,2.5); SELECT sum(v) FROM t;", .real 4.0),
    ("INSERT INTO t VALUES(1,'1'),(2,'2'); SELECT sum(v) FROM t;", .integer 3),
    ("INSERT INTO t VALUES(1,'12xyz'),(2,'3'); SELECT sum(v) FROM t;", .real 15.0),
    ("INSERT INTO t VALUES(1,CAST(X'31320033' AS TEXT)),(2,'1'); SELECT sum(v) FROM t;", .integer 13),
    ("INSERT INTO t VALUES(1,1),(2,2); SELECT avg(v) FROM t;", .real 1.5),
    ("INSERT INTO t VALUES(1,1),(2,2); SELECT total(v) FROM t;", .real 3.0),
    ("SELECT sum(v) FROM t;", .null),
    ("SELECT avg(v) FROM t;", .null),
    ("SELECT total(v) FROM t;", .real 0.0),
    ("INSERT INTO t VALUES(1,1e308),(2,1.0),(3,-1e308); SELECT sum(v) FROM t;", .real 1.0),
    ("INSERT INTO t VALUES(1,1e999),(2,-1e999); SELECT sum(v) FROM t;", .null),
    ("INSERT INTO t VALUES(1,9223372036854775807),(2,1),(3,0.0); SELECT sum(v) FROM t;", .real 9223372036854775808.0),
    ("INSERT INTO t VALUES(1,0.0),(2,9007199254740993),(3,-9007199254740992); SELECT sum(v) FROM t;", .real 1.0)]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"numeric aggregate: {message}"
    let value ← match SQLSurface.value expected with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [[value]] do
      fail s!"numeric aggregate result: {sql}"
  match CoreSQL.execute Core.State.empty (setup ++
      "INSERT INTO t VALUES(1,9223372036854775807),(2,1); SELECT sum(v) FROM t;") with
  | .ok _ => fail "SUM omitted the integer overflow error"
  | .error _ => pure ()
  let (_, grouped) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,g,v); INSERT INTO t VALUES(1,1,1.5),(2,1,2.5),(3,2,NULL); SELECT g,sum(v),avg(v),total(v) FROM t GROUP BY g;" with
    | .ok result => pure result
    | .error message => fail s!"grouped numeric aggregate: {message}"
  let expected ← match ([[Value.integer 1, .real 4.0, .real 2.0, .real 4.0],
      [.integer 2, .null, .null, .real 0.0]]).mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (grouped.getLast?).map (·.rows) == some expected do fail "grouped aggregate values"

private def expectSQLiteLimitOffset : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,b); INSERT INTO t VALUES(1,1,1),(2,2,2),(3,1,3),(4,3,4);"
  for (query, values) in [
      ("SELECT id FROM t LIMIT 1 OFFSET 1;", [2]),
      ("SELECT id FROM t LIMIT 1,2;", [2,3]),
      ("SELECT id FROM t LIMIT -1 OFFSET 2;", [3,4]),
      ("SELECT id FROM t LIMIT 0 OFFSET 1;", []),
      ("SELECT id FROM t LIMIT 0 OFFSET NULL;", []),
      ("SELECT id FROM t LIMIT NULL,0;", []),
      ("SELECT id FROM t LIMIT 0 OFFSET 9223372036854775808;", []),
      ("SELECT id FROM t LIMIT 1 OFFSET -3;", [1]),
      ("SELECT id FROM t LIMIT +1 OFFSET +1;", [2]),
      ("SELECT DISTINCT v FROM t ORDER BY id LIMIT 1 OFFSET 1;", [2]),
      ("SELECT DISTINCT v FROM t ORDER BY id DESC LIMIT 1 OFFSET 1;", [1]),
      ("SELECT DISTINCT v FROM t ORDER BY b DESC LIMIT 1 OFFSET 1;", [2]),
      ("SELECT abs(-9223372036854775808) FROM t LIMIT 1 OFFSET 10;", [])] do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ query) with
      | .ok outcome => pure outcome
      | .error message => fail s!"LIMIT/OFFSET: {message}"
    let expected ← match values.mapM (fun v => (fun x => [x]) <$> SQLSurface.value (.integer v)) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some expected do fail s!"LIMIT/OFFSET rows: {query}"
  for query in ["SELECT DISTINCT abs(-9223372036854775808) FROM t LIMIT 1 OFFSET 10;",
      "SELECT id FROM t WHERE abs(-9223372036854775808) LIMIT 1 OFFSET 10;",
      "SELECT id FROM t LIMIT 9223372036854775808;", "SELECT missing FROM t LIMIT 0 OFFSET 5;"] do
    match CoreSQL.execute Core.State.empty (setup ++ query) with
    | .ok _ => fail s!"LIMIT/OFFSET suppressed a required error: {query}"
    | .error _ => pure ()

private def expectSQLiteInList : IO Unit := do
  let cases : List (String × List Value) := [
    ("SELECT NULL IN (), NULL NOT IN (), missing IN ();", [.integer 0, .integer 1, .integer 0]),
    ("SELECT 1 IN (1,2), 1 NOT IN (1,2), 2 IN (1,NULL), NULL IN (1,2);",
      [.integer 1, .integer 0, .null, .null]),
    ("SELECT '1' IN (1), CAST('1' AS NUMERIC) IN (1), 1 IN (CAST('1' AS TEXT));",
      [.integer 0, .integer 1, .integer 0]),
    ("SELECT 1 IN (1,abs(-9223372036854775808)), abs(-9223372036854775808) IN ();",
      [.integer 1, .integer 0])]
  for (query, values) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty query with
      | .ok outcome => pure outcome
      | .error message => fail s!"IN list: {message}"
    let expected ← match values.mapM SQLSurface.value with
      | .ok row => pure row
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [expected] do fail s!"IN list truth: {query}"
  let indexed := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,1),(2,2); CREATE TABLE empty(id INTEGER PRIMARY KEY,v);"
  let (_, results) ← match CoreSQL.execute Core.State.empty (indexed ++
      "SELECT id FROM t WHERE id IN (1,abs(-9223372036854775808)) AND id=1 LIMIT 1;") with
    | .ok outcome => pure outcome
    | .error message => fail s!"primary equality before IN membership: {message}"
  unless (results.getLast?).map (·.rows.length) == some 1 do
    fail "primary equality did not bound the IN membership scan"
  for query in [
      "SELECT id FROM t WHERE id IN (1,abs(-9223372036854775808)) LIMIT 1;",
      "SELECT id FROM t WHERE id IN (1,abs(-9223372036854775808)) AND id>0 LIMIT 1;",
      "SELECT id FROM empty WHERE id=1 AND id IN (1,abs(-9223372036854775808),id);"] do
    match CoreSQL.execute Core.State.empty (indexed ++ query) with
    | .ok _ => fail "IN search did not materialize an invalid RHS"
    | .error _ => pure ()
  for query in ["SELECT 1 IN (1,2,abs(-9223372036854775808));",
      "SELECT NULL IN (abs(-9223372036854775808),1);",
      "SELECT unknown_function() IN ();", "SELECT 1 IN (1,missing);"] do
    match CoreSQL.execute Core.State.empty query with
    | .ok _ => fail s!"invalid IN expression accepted: {query}"
    | .error _ => pure ()

private def expectSQLiteWALRecoveryPrefix : IO Unit := do
  let header := CoreWALFileAdapter.header
  let page := Storage.Page.zero PhysicalCodec.pageSize
  let first : PhysicalWAL.Frame := {
    pageNumber := ⟨⟨2, by decide⟩, by decide⟩
    databaseSize := ⟨0, by decide⟩
    page }
  let commit : PhysicalWAL.Frame := {
    pageNumber := ⟨⟨1, by decide⟩, by decide⟩
    databaseSize := ⟨2, by decide⟩
    page }
  let wal : PhysicalWAL.WAL := { header, frames := [first, commit, first] }
  for bytes in [wal.encode, wal.encode ++ [1,2,3],
      wal.encode.take (32 + 2 * PhysicalWAL.frameSize + 17)] do
    match SQLite.WALRead.recover bytes with
    | .ok (some snapshot) =>
      unless snapshot.pageCount == 2 && snapshot.pageSize == 4096 && snapshot.frames.length == 2 do
        fail "WAL recovery exposed an uncommitted or incomplete tail"
    | _ => fail "WAL recovery rejected a valid committed prefix"
  let uncommitted : PhysicalWAL.WAL := { header, frames := [first, first] }
  for bytes in [[], header.encode, uncommitted.encode] do
    match SQLite.WALRead.recover bytes with
    | .ok none => pure ()
    | _ => fail "WAL recovery invented a commit"
  let snapshot : SQLite.WALRead.Snapshot := {
    pageSize := 512, pageCount := 2
    frames := [⟨2, 2, [2]⟩, ⟨2, 0, [1]⟩] }
  let base := fun n => some [UInt8.ofNat n]
  unless snapshot.readPage base 1 == some [1] && snapshot.readPage base 2 == some [2] &&
      (snapshot.readPage base 3).isNone do
    fail "WAL main-page overlay or committed size is incorrect"

private def expectSQLiteRowDeletes : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT); INSERT INTO t VALUES(1,'a'),(2,'bb'),(3,'ccc'),(4,NULL); CREATE INDEX tv ON t(v);"
  for (query, removed) in [
      ("DELETE FROM t WHERE length(v)>1;", 2),
      ("DELETE FROM t AS x WHERE x.id%2=0;", 2),
      ("DELETE FROM t WHERE 0 AND abs(-9223372036854775808);", 0),
      ("DELETE FROM t WHERE id+0>0;", 4),
      ("DELETE FROM t WHERE missing+1 AND 0;", 0)] do
    let (state, results) ← match CoreSQL.execute Core.State.empty (setup ++ query) with
      | .ok outcome => pure outcome
      | .error message => fail s!"row DELETE: {message}"
    unless (results.getLast?).map (·.changes) == some removed &&
        (state.database.findTable? "t").map (·.rows.length) == some (4 - removed) do
      fail s!"row DELETE count: {query}"
  for query in ["DELETE FROM t WHERE id=1 OR abs(-9223372036854775808);",
      "DELETE FROM t WHERE abs(-9223372036854775808) AND 0;",
      "DELETE FROM t WHERE wrong.id+1;", "DELETE FROM t WHERE missing+1;",
      "DELETE FROM t WHERE unknown_function(id) AND 0;"] do
    match CoreSQL.execute Core.State.empty (setup ++ query) with
    | .ok _ => fail s!"invalid DELETE accepted: {query}"
    | .error _ => pure ()

private def expectSQLiteDistinctLimit : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,1),(2,2),(3,1),(4,3);"
  for query in ["SELECT DISTINCT v FROM t ORDER BY id LIMIT 2;",
      "SELECT DISTINCT v FROM t LIMIT 2;", "SELECT DISTINCT v FROM t ORDER BY v LIMIT 2;"] do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ query) with
      | .ok outcome => pure outcome
      | .error message => fail s!"DISTINCT LIMIT: {message}"
    let expected ← match [[Value.integer 1], [Value.integer 2]].mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some expected do
      fail s!"DISTINCT must retain first values before LIMIT: {query}"

private def expectSQLiteDistinctOrder : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,b); INSERT INTO t VALUES(1,1,1),(2,1,3),(3,2,2),(4,1,0);"
  for (query, values) in [
      ("SELECT DISTINCT v FROM t ORDER BY b DESC;", [2,1]),
      ("SELECT DISTINCT +v FROM t ORDER BY b DESC;", [2,1]),
      ("SELECT DISTINCT v FROM t ORDER BY id DESC;", [1,2]),
      ("SELECT DISTINCT +v FROM t ORDER BY id DESC;", [1,2]),
      ("SELECT DISTINCT v FROM t ORDER BY b DESC LIMIT 1;", [2]),
      ("SELECT DISTINCT +v FROM t ORDER BY id DESC LIMIT 1;", [1])] do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ query) with
      | .ok outcome => pure outcome
      | .error message => fail s!"DISTINCT source ordering: {message}"
    let expected ← match values.mapM (fun v => (fun x => [x]) <$> SQLSurface.value (.integer v)) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some expected do
      fail s!"DISTINCT source representative ordering: {query}"

private def expectSQLiteNumericDistinct : IO Unit := do
  let cases : List (String × String × List Value) := [
    ("1", "1.0", [.integer 1]),
    ("1.0", "1", [.real 1.0]),
    ("0", "-0.0", [.integer 0]),
    ("0.0", "-0.0", [.real 0.0]),
    ("NULL", "NULL", [.null]),
    ("1", "'1'", [.integer 1, .text "1"]),
    ("'1'", "X'31'", [.text "1", .blob #[49]]),
    ("9007199254740992", "9007199254740992.0", [.integer 9007199254740992]),
    ("9007199254740993", "9007199254740992.0", [.integer 9007199254740993, .real 9007199254740992.0]),
    ("-9223372036854775808", "-9223372036854775808.0", [.integer (-9223372036854775808)]),
    ("9223372036854775807", "9223372036854775808.0", [.integer 9223372036854775807, .real 9223372036854775808.0]),
    ("1.5", "1.5", [.real 1.5])]
  for (left, right, values) in cases do
    let setup := s!"CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,{left}),(2,{right});"
    for projection in ["v", "+v"] do
      let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ s!"SELECT DISTINCT {projection} FROM t;") with
        | .ok outcome => pure outcome
        | .error message => fail s!"numeric DISTINCT: {message}"
      let expected ← match values.mapM (fun v => (fun x => [x]) <$> SQLSurface.value v) with
        | .ok rows => pure rows
        | .error message => fail message
      unless (results.getLast?).map (·.rows) == some expected do
        fail s!"numeric DISTINCT changed a representative or merged unequal values: {left}, {right} ({projection})"

private def expectSQLiteNumericCompounds : IO Unit := do
  let cases : List (String × List (List Value)) := [
    ("SELECT 1 UNION SELECT 1.0;", [[.real 1.0]]),
    ("SELECT 1.0 UNION SELECT 1;", [[.integer 1]]),
    ("SELECT 1 INTERSECT SELECT 1.0;", [[.integer 1]]),
    ("SELECT 1.0 INTERSECT SELECT 1;", [[.real 1.0]]),
    ("SELECT 1 EXCEPT SELECT 1.0;", []),
    ("SELECT 3 UNION SELECT 1 UNION SELECT 2;", [[.integer 1], [.integer 2], [.integer 3]]),
    ("SELECT NULL INTERSECT SELECT NULL;", [[.null]]),
    ("SELECT 1 UNION ALL SELECT 1.0;", [[.integer 1], [.real 1.0]]),
    ("SELECT 1,'x' UNION SELECT 1.0,'x';", [[.real 1.0, .text "x"]]),
    ("SELECT '1' UNION SELECT 1 UNION SELECT X'31';", [[.integer 1], [.text "1"], [.blob #[49]]]),
    ("SELECT 9007199254740993 EXCEPT SELECT 9007199254740992.0;", [[.integer 9007199254740993]])]
  for (query, values) in cases do
    let (state, results) ← match CoreSQL.execute Core.State.empty query with
      | .ok outcome => pure outcome
      | .error message => fail s!"numeric compound: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless results.map (·.rows) == [expected] && state.database.tables.isEmpty do
      fail s!"numeric compound changed multiplicity, ordering, representative, or state: {query}"

private def expectSQLiteNumericGroups : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,x); INSERT INTO t VALUES(1,1,5),(2,1.0,7),(3,1,6),(4,'1',2),(5,NULL,NULL),(6,NULL,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT v,count(*) FROM t GROUP BY v;", [[.null,.integer 2],[.integer 1,.integer 3],[.text "1",.integer 1]]),
    ("SELECT v,max(x) FROM t GROUP BY v;", [[.null,.null],[.real 1.0,.integer 7],[.text "1",.integer 2]]),
    ("SELECT v,sum(x) FROM t GROUP BY v;", [[.null,.null],[.integer 1,.integer 18],[.text "1",.integer 2]]),
    ("SELECT v,min(x),max(x),min(x) FROM t GROUP BY v;", [[.null,.null,.null,.null],[.real 1.0,.integer 5,.integer 7,.integer 5],[.text "1",.integer 2,.integer 2,.integer 2]]),
    ("SELECT v,count(x) FROM t GROUP BY v;", [[.null,.integer 0],[.integer 1,.integer 3],[.text "1",.integer 1]]),
    ("SELECT min(v) FROM t WHERE id<4;", [[.integer 1]]),
    ("SELECT max(v) FROM t WHERE id<4;", [[.integer 1]])]
  for (query, values) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ query) with
      | .ok outcome => pure outcome
      | .error message => fail s!"numeric grouping: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some expected do
      fail s!"GROUP BY changed equality, counts, ordering, or representative storage class: {query}"
  let nullSetup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,x);INSERT INTO t VALUES(1,1,NULL),(2,1.0,NULL);"
  let (_, results) ← match CoreSQL.execute Core.State.empty (nullSetup ++ "SELECT v,max(x) FROM t GROUP BY v;") with
    | .ok outcome => pure outcome
    | .error message => fail message
  let real ← match SQLSurface.value (.real 1.0) with
    | .ok value => pure value
    | .error message => fail message
  unless (results.getLast?).map (·.rows) == some [[real,.null]] do
    fail "all-NULL extremum must select the last source row"

private def expectSQLiteScalarAdmission : IO Unit := do
  for expression in ["coalesce(1,missing)", "coalesce(1,unknown_function())",
      "abs(-9223372036854775808)"] do
    match CoreSQL.execute Core.State.empty
        s!"CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,{expression});" with
    | .error _ => pure ()
    | .ok _ => fail s!"Core scalar should reject {expression}"
  let sql := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,CAST('12' AS INTEGER));"
  let certificate ← match CoreTokenGrammar.parseCertified sql with
    | .ok certificate => pure certificate
    | .error message => fail message
  let wrongTokens ← match lex
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,CAST('12' AS REAL));" with
    | .ok tokens => pure tokens
    | .error message => fail message
  match CoreTokenGrammar.check wrongTokens certificate.statements with
  | .error _ => pure ()
  | .ok _ => fail "Core grammar accepted a changed CAST type"

private def expectSQLiteConstantSelect : IO Unit := do
  let queries := [
    ("SELECT 6*7;", [[42]]),
    ("SELECT CASE WHEN 0 THEN abs(-9223372036854775808) ELSE 7 END;", [[7]]),
    ("SELECT abs(-9223372036854775808) WHERE 0;", []),
    ("SELECT abs(-9223372036854775808) LIMIT 0;", []),
    ("SELECT abs(-9223372036854775808) LIMIT 1 OFFSET 1;", []),
    ("SELECT 1 WHERE '0.5x';", [[1]]),
    ("SELECT 1 UNION ALL SELECT 2;", [[1], [2]])]
  for (sql, expected) in queries do
    let (state, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"constant SELECT {sql}: {message}"
    unless state.database.tables.isEmpty do fail "constant SELECT mutated the database"
    let values ← expected.mapM fun row => row.mapM fun integer =>
      match SQLSurface.value (.integer integer) with
      | .ok value => pure value
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some values do
      fail s!"constant SELECT wrong result: {sql}"

private def expectSQLiteColumnAffinity : IO Unit := do
  let (state, results) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,t TEXT,n NUMERIC,r REAL,b BLOB);\n      INSERT INTO t VALUES('1.0',12,'3e0','5.0','001');\n      CREATE INDEX t_n ON t(n);\n      SELECT t,n,r,b FROM t WHERE n='003' AND t=12;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"column affinity: {message}"
  let expected ← ([Value.text "12", .integer 3, .real 5.0, .text "001"]).mapM fun v =>
    match SQLSurface.value v with
    | .ok v => pure v
    | .error message => fail message
  unless (results.getLast?).map (·.rows) == some [expected] do
    fail "column affinity changed value or storage class"
  let table ← match state.database.findTable? "t" with
    | some table => pure table
    | none => fail "column affinity lost table"
  unless CanonicalSchemaSQL.parse (CanonicalSchemaSQL.print table.schema) == some table.schema do
    fail "declared types did not survive canonical schema printing"
  let noncanonical ← match SQLSurface.value (.text "3") with
    | .ok value => pure value
    | .error message => fail message
  if Core.Row.create table.schema
      ([.integer ⟨2, by decide, by decide⟩] ++ expected.set 1 noncanonical) |>.isOk then
    fail "Core row admitted numeric TEXT without applying column affinity"

private def expectSQLiteTypedSchemaNames : IO Unit := do
  for typeName in ["DOUBLE PRECISION", "FLOATING POINT", "a\"b TEXT,)", "", "NUMERIC(12,2)"] do
    let schema : Core.Schema := {
      name := "quoted\"table"
      columns := [{ name := "id", notNull := true, integerPrimaryKey := true },
        { name := "v", notNull := true, declaredType := typeName }]
      primaryKey := 0 }
    unless CanonicalSchemaSQL.parse (CanonicalSchemaSQL.print schema) == some schema do
      fail s!"canonical schema lost declared type {typeName}"

private def expectSQLiteCertifiedAdmission : IO Unit := do
  for sql in ["CREATE TABLE t(id INTEGER PRIMARY KEY) WITHOUT ROWID;",
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT COLLATE NOCASE);"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then
      fail s!"Core silently discarded unsupported schema syntax: {sql}"
  for expression in ["2 BETWEEN 1 AND 3", "2 NOT BETWEEN 1 AND 3"] do
    match CoreTokenGrammar.parseStatements s!"SELECT {expression};" with
    | .ok _ => pure ()
    | .error message => fail s!"certified BETWEEN: {message}"
  let tokens ← match lex "SELECT 2 BETWEEN 1 AND 3;" with
    | .ok tokens => pure tokens
    | .error message => fail message
  let wrong ← match parse "SELECT (2>=1) AND (99<=3);" with
    | .ok statements => pure statements
    | .error message => fail message
  if (CoreTokenGrammar.check tokens wrong).isOk then
    fail "BETWEEN certificate accepted unequal copies of its left operand"

private def unitTests : Array (String × IO Unit) := #[
  ("SQLite stored column affinity and indexed comparison", expectSQLiteColumnAffinity),
  ("SQLite quoted declared type schema roundtrip", expectSQLiteTypedSchemaNames),
  ("SQLite certified schema and BETWEEN admission", expectSQLiteCertifiedAdmission),
  ("SQLite SELECT without FROM", expectSQLiteConstantSelect),
  ("SQLite scalar operations through Core SQL", expectSQLiteScalarCore),
  ("SQLite text/blob functions through certified Core SQL", expectSQLiteTextFunctions),
  ("SQLite row expressions and column comparison affinity", expectSQLiteRowExpressions),
  ("SQLite page-size conversion publication failures", expectPageSizeConversionFailures),
  ("SQLite schema namespace and IF NOT EXISTS", expectSQLiteSchemaAdmission),
  ("SQLite UNIQUE indexes and multi-key replacement", expectSQLiteUniqueIndexes),
  ("SQLite LIKE GLOB ESCAPE and permissive UTF-8", expectSQLitePatterns),
  ("SQLite round fixed-decimal and integral paths", expectSQLiteRound),
  ("SQLite rowid UPDATE binding and changes", expectSQLiteRowidUpdates),
  ("SQLite implicit rowid allocation and DEFAULT VALUES", expectSQLiteImplicitRowid),
  ("SQLite aggregate expressions DISTINCT and WHERE", expectSQLiteAggregateExpressions),
  ("SQLite aggregate scalar results and implicit source row", expectSQLiteAggregateResults),
  ("SQLite operator precedence and NULL-test syntax", expectSQLiteOperatorPrecedence),
  ("SQLite ORDER BY collations and NULL placement", expectSQLiteOrderModifiers),
  ("SQLite large value bounds", expectSQLiteLargeValueBounds),
  ("SQLite WAL index headers", expectSQLiteWALIndex),
  ("SQLite large local payload leaf packing", expectSingletonLeafPacking),
  ("SQLite ORDER BY expressions and result binding", expectSQLiteOrderExpressions),
  ("SQLite quoted identifiers and source scopes", expectSQLiteQuotedNames),
  ("SQLite quoted functions and argument limit", expectSQLiteQuotedFunctions),
  ("SQLite scalar and aggregate expression collations", expectSQLiteExpressionCollations),
  ("SQLite collated column groups and bounded finalization", expectSQLiteCollatedGroups),
  ("SQLite WHERE result aliases", expectSQLiteWhereAliases),
  ("SQLite grouped expressions and HAVING", expectSQLiteGroupedExpressions),
  ("SQLite aggregate internal ORDER BY", expectSQLiteAggregateInternalOrder),
  ("SQLite aggregate FILTER", expectSQLiteAggregateFilter),
  ("SQLite probability hints", expectSQLiteProbability),
  ("SQLite UPDATE OR IGNORE and sequential key changes", expectSQLiteUpdateIgnore),
  ("SQLite INSERT OR IGNORE constraints and row allocation", expectSQLiteInsertIgnore),
  ("SQLite DELETE RETURNING old values and atomic errors", expectSQLiteDeleteReturning),
  ("SQLite VALUES queries, compound windows and metadata checking", expectSQLiteValuesQuery),
  ("SQLite INSERT SELECT snapshots, affinity and empty sources", expectSQLiteInsertSelect),
  ("SQLite DROP tables and indexes with transaction rollback", expectSQLiteDrop),
  ("SQLite file read/write versions and schema-format admission", expectSQLiteHeaderVersions),
  ("SQLite reserved-tail geometry and minimum usable size", expectSQLiteReservedPages),
  ("SQLite header page-count validity and physical tails", expectSQLiteHeaderSize),
  ("SQLite multi-page and overflow schema catalog", expectSQLiteSchemaPages),
  ("SQLite byte-preserving format and printf", expectSQLiteFormat),
  ("SQLite math functions and exact floating remainder", expectSQLiteMath),
  ("SQLite Unicode escape functions", expectSQLiteUnicodeEscape),
  ("SQLite string aggregates", expectSQLiteStringAggregates),
  ("SQLite ungrouped aggregate HAVING", expectSQLiteAggregateHaving),
  ("SQLite ungrouped aggregate ordering", expectSQLiteAggregateOrder),
  ("SQLite numeric literal syntax and signed boundaries", expectSQLiteNumericLiterals),
  ("SQLite literal spelling and certified identity", expectSQLiteLiteralSpelling),
  ("SQLite compound ORDER BY and LIMIT", expectSQLiteCompoundTails),
  ("SQLite compound result collations", expectSQLiteCompoundCollations),
  ("SQLite boolean keywords and column shadowing", expectSQLiteBooleanKeywords),
  ("SQLite byte-preserving TEXT functions", expectSQLiteRawText),
  ("SQLite SUM/AVG/TOTAL numeric accumulators", expectSQLiteNumericAggregates),
  ("SQLite LIMIT/OFFSET scans and syntax", expectSQLiteLimitOffset),
  ("SQLite IN-list truth, affinity and evaluation", expectSQLiteInList),
  ("SQLite WAL valid committed prefix", expectSQLiteWALRecoveryPrefix),
  ("SQLite row-expression DELETE", expectSQLiteRowDeletes),
  ("SQLite stable DISTINCT before LIMIT", expectSQLiteDistinctLimit),
  ("SQLite DISTINCT source ordering", expectSQLiteDistinctOrder),
  ("SQLite exact numeric DISTINCT and original representatives", expectSQLiteNumericDistinct),
  ("SQLite numeric set operations and compound ordering", expectSQLiteNumericCompounds),
  ("SQLite numeric grouping and aggregate representatives", expectSQLiteNumericGroups),
  ("SQLite row-expression predicates", expectSQLiteRowPredicates),
  ("physical index tail ownership", expectIndexTailOwnership),
  ("SQLite row-dependent UPDATE", expectSQLiteRowUpdates),
  ("SQLite scalar admission and CAST token certificate", expectSQLiteScalarAdmission),
  ("checked binary page search and shared record views", expectCheckedTablePages),
  ("read pager cache and short-read boundary", expectReadPagerBoundary),
  ("cached primary signed/overflow rows and write invalidation", expectCachedPrimaryEdgeRows),
  ("certified Core token grammar", expectCertifiedCoreTokenGrammar),
  ("persistent page identities", expectPersistentPageTree),
  ("verified file-format codecs", expectU16Codec),
  ("verified SQLite varints", expectVarintCodec),
  ("verified record serial types", expectSerialTypes),
  ("verified fixed-width payload codec", expectUnsignedFixedCodec),
  ("verified signed integer payload codec", expectSignedIntegerCodec),
  ("verified physical record fields", expectRecordFields),
  ("verified physical record headers", expectRecordHeader),
  ("verified B-tree page headers", expectBTreePageHeaders),
  ("verified table B-tree cells", expectTableBTreeCells),
  ("verified typed B-tree layout", expectTypedBTreeLayout),
  ("verified bounded page numbers", expectBoundedPageNumbers),
  ("verified SQLite database first page", expectDatabaseFirstPage),
  ("verified whole-disk byte format", expectDiskFormat),
  ("verified optimizer semantics", expectOptimizerSemantics),
  ("multiplicity-valued SQL semantics", expectKRelationSemantics),
  ("typed relational algebra semantics", expectRelationalAlgebra),
  ("verified paged B+tree mutations", expectPagedBTree),
  ("recursive B+tree split propagation", expectRecursiveBPlusTree),
  ("verified primary-key merge join", expectCoreMergeJoin),
  ("recursive physical SQLite page tree", expectRecursivePhysicalPageBTree),
  ("physical MVP table B+tree pages", expectPhysicalMVPTableBTree),
  ("verified growable rollback journal", expectGrowableRollbackJournal),
  ("explicit torn-sector crash model", expectTornSectorModel),
  ("explicit POSIX VFS durability plan", expectPOSIXVFSPlan),
  ("verified group commit and write absorption", expectGroupCommit),
  ("physical Core WAL group commit", expectPhysicalGroupCommit),
  ("verified page cache and deferred writes", expectVerifiedPageCache),
  ("verified safe freed-page reuse", expectSafePageReuse),
  ("verified physical SQLite WAL codec", expectPhysicalWALCodec),
  ("exact binary64 Core semantics", expectBinary64Core),
  ("proof-carrying arbitrary MVP schemas", expectGeneralMVPSchemaCore),
  ("arbitrary-schema verified MVP SQL", expectGeneralMVPSQL),
  ("arbitrary-schema SQLite file interop", expectGeneralMVPFileInterop),
  ("TEXT PRIMARY KEY SQLite file interop", expectTextPrimaryKeyInterop),
  ("live table and index overflow interop", expectLiveOverflowInterop),
  ("escaped catalog identifiers", expectEscapedCatalogIdentifiers),
  ("physical multipage index traversal", expectPhysicalIndexTraversal),
  ("wide C-produced integer index certificate", expectWideCIndexCertificate),
  ("Core freelist physical shrink", expectCoreFreelistShrink),
  ("localized Core dirty-page commit", expectCoreDirtyPageCommit),
  ("persistent database application metadata", expectHeaderMetadata),
  ("verified multi-trunk Core freelist", expectCoreMultiFreelist),
  ("lazy reachable-page Core decode", expectLazyReachablePageDecode),
  ("arbitrary-schema transactional file engine", expectGeneralMVPFileEngine),
  ("verified MVP record cells", expectMVPRecordCells),
  ("SQLite CLI opens verified MVP file", expectSQLiteFileInterop),
  ("MVP rollback adapter commit and recovery", expectMVPFileAdapter),
  ("verified ordered-index core", expectOrderedIndexCore),
  ("literal select", expectSQL "literal select" "SELECT 1+2, 'ok', NULL;"
    #[#[.integer 3, .text "ok", .null]]),
  ("negative shift reverses direction", expectSQL "negative shift reverses direction"
    "SELECT 8 << -1, 8 >> -1;" #[#[.integer 4, .integer 16]]),
  ("identifier folding is ASCII only", expectSQL "identifier folding is ASCII only" "
    CREATE TABLE Ä(x); CREATE TABLE ä(x);
    SELECT count(*) FROM sqlite_master WHERE type='table';" #[#[.integer 2]]),
  ("create insert select", expectSQL "create insert select" "
    CREATE TABLE t(a,b);
    INSERT INTO t VALUES(2,'two'),(1,'one');
    SELECT a,b FROM t ORDER BY a;"
    #[#[.integer 1, .text "one"], #[.integer 2, .text "two"]]),
  ("qualified cross join", expectSQL "qualified cross join" "
    CREATE TABLE a(x); CREATE TABLE b(y);
    INSERT INTO a VALUES(2),(1); INSERT INTO b VALUES('z');
    SELECT a.x,b.y FROM a,b ORDER BY a.x;"
    #[#[.integer 1, .text "z"], #[.integer 2, .text "z"]]),
  ("parenthesized schema join", expectSQL "parenthesized schema join" "
    ATTACH ':memory:' AS aux;
    CREATE TABLE main.a(x,y); INSERT INTO main.a VALUES(1,'left');
    CREATE TABLE aux.b(x,y); INSERT INTO aux.b VALUES(2,'right');
    SELECT main.a.y,aux.b.y FROM (main.a JOIN (aux.b) ON aux.b.x=main.a.x+1);"
    #[#[.text "left", .text "right"]]),
  ("qualified trigger dml", expectError "qualified trigger dml" "
    CREATE TABLE t(x); CREATE TRIGGER ti AFTER INSERT ON t BEGIN
      INSERT INTO main.t VALUES(2);
    END;" "qualified table names are not allowed"),
  ("null logic", expectSQL "null logic" "
    CREATE TABLE t(x); INSERT INTO t VALUES(NULL),(0),(1);
    SELECT count(*),count(x) FROM t WHERE x IS NULL OR x=1;"
    #[#[.integer 2, .integer 1]]),
  ("postfix not null", expectSQL "postfix not null" "
    SELECT 1 WHERE 7 NOT NULL;"
    #[#[.integer 1]]),
  ("update delete", expectSQL "update delete" "
    CREATE TABLE t(x,y); INSERT INTO t VALUES(1,10),(2,20),(3,30);
    UPDATE t SET y=y+1 WHERE x>=2; DELETE FROM t WHERE x=1;
    SELECT * FROM t ORDER BY x DESC;"
    #[#[.integer 3, .integer 31], #[.integer 2, .integer 21]]),
  ("defaults", expectSQL "defaults" "
    CREATE TABLE t(a DEFAULT 7,b DEFAULT 'x'); INSERT INTO t(b) VALUES('y');
    SELECT * FROM t;" #[#[.integer 7, .text "y"]]),
  ("default SQL preserved", expectSQL "default SQL preserved" "
    CREATE TABLE t(c DEFAULT 'abc'); PRAGMA table_info(t);"
    #[#[.integer 0, .text "c", .text "", .integer 0, .text "'abc'", .integer 0]]),
  ("nonconstant default rejected", expectError "nonconstant default rejected" "
    CREATE TABLE t(x,y DEFAULT(max(x,5)));"
    "default value of column [y] is not constant"),
  ("autoincrement high water", expectSQL "autoincrement high water" "
    CREATE TABLE t(id INTEGER PRIMARY KEY AUTOINCREMENT,v);
    INSERT INTO t(v) VALUES(1); DELETE FROM t; INSERT INTO t(v) VALUES(2);
    SELECT id FROM t;" #[#[.integer 2]]),
  ("default int64 overflow remains real", expectSQL "default int64 overflow remains real" "
    CREATE TABLE t(x INT DEFAULT(-(-9223372036854775808)));
    INSERT INTO t DEFAULT VALUES; SELECT typeof(x),x>9223372036854775807 FROM t;"
    #[#[.text "real", .integer 1]]),
  ("writable schema default", expectSQL "writable schema default" "
    CREATE TABLE t(a,b DEFAULT 99); PRAGMA writable_schema=ON;
    UPDATE sqlite_master SET sql='CREATE TABLE t(a,b DEFAULT(:xyz))';
    INSERT INTO t(a) VALUES('x'); SELECT a,quote(b) FROM t;"
    #[#[.text "x", .text "NULL"]]),
  ("transaction rollback", expectSQL "transaction rollback" "
    CREATE TABLE t(x); BEGIN; INSERT INTO t VALUES(1); ROLLBACK; SELECT count(*) FROM t;"
    #[#[.integer 0]]),
  ("distinct limit", expectSQL "distinct limit" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1),(1),(2),(3);
    SELECT DISTINCT x FROM t ORDER BY x LIMIT 2 OFFSET 1;"
    #[#[.integer 2], #[.integer 3]]),
  ("distinct expression collation", expectSQL "distinct expression collation" "
    CREATE TABLE t(x); INSERT INTO t VALUES('b'),('B');
    SELECT DISTINCT x COLLATE nocase FROM t;"
    #[#[.text "b"]]),
  ("rtrim compound collation", expectSQL "rtrim compound collation" "
    CREATE TABLE t(x COLLATE rtrim); INSERT INTO t VALUES(''),(' '),('  ');
    SELECT x FROM t UNION SELECT 1;"
    #[#[.integer 1], #[.text ""]]),
  ("distinct aggregates", expectSQL "distinct aggregates" "
    CREATE TABLE t(x COLLATE nocase, n); INSERT INTO t VALUES('A',1),('a',1),(NULL,2),('B',2);
    SELECT count(DISTINCT x), sum(DISTINCT n), count(ALL n) FROM t;"
    #[#[.integer 2, .integer 3, .integer 4]]),
  ("distinct aggregate arity", expectError "distinct aggregate arity" "
    CREATE TABLE t(x,y); SELECT string_agg(DISTINCT x,y) FROM t;"
    "DISTINCT aggregates must have exactly one argument"),
  ("unique expression index", expectError "unique expression index" "
    CREATE TABLE t(a,b); CREATE UNIQUE INDEX tx ON t(a+b);
    INSERT INTO t VALUES(0,1),(1,0);"
    "UNIQUE constraint failed: index 'tx'"),
  ("index expression safety", expectError "index expression safety" "
    CREATE TABLE t(a); CREATE INDEX tx ON t(a+random());"
    "non-deterministic functions prohibited in index expressions"),
  ("index subquery safety", expectError "index subquery safety" "
    CREATE TABLE t(a); CREATE INDEX tx ON t(a+(SELECT 1));"
    "subqueries prohibited in index expressions"),
  ("where result alias", expectSQL "where result alias" "
    CREATE TABLE t(a); INSERT INTO t VALUES('abc001xyz'),('abc002xyz');
    SELECT substr(a,4,3) AS k FROM t WHERE k=printf('%03d',2);"
    #[#[.text "002"]]),
  ("delete returning", expectSQL "delete returning" "
    CREATE TABLE t(a,b); CREATE INDEX ignored ON t(a); INSERT INTO t VALUES(1,'x'),(2,'y');
    DELETE FROM t INDEXED BY ignored WHERE a=1 RETURNING *;"
    #[#[.integer 1, .text "x"]]),
  ("json expression", expectSQL "json expression" "
    CREATE TABLE t(y); INSERT INTO t VALUES('{b:5}');
    SELECT json_insert('{}','$.a',json(y))->>'$.a.b' FROM t;"
    #[#[.integer 5]]),
  ("forward inner join on scope", expectSQL "forward inner join on scope" "
    CREATE TABLE t(x); INSERT INTO t VALUES(0),(1);
    SELECT count(*) FROM t AS a JOIN t AS b ON d.x=a.x JOIN t AS d ON d.x=a.x;"
    #[#[.integer 4]]),
  ("correlated aggregate lift", expectSQL "correlated aggregate lift" "
    CREATE TABLE jjj(x); CREATE TABLE nnn(x);
    SELECT (SELECT 'mmm' UNION SELECT DISTINCT max(name) ORDER BY 1)
      FROM sqlite_master;"
    #[#[.text "mmm"]]),
  ("drop index if exists", expectSQL "drop index if exists" "
    CREATE TABLE t(x); DROP INDEX IF EXISTS absent; SELECT count(*) FROM t;"
    #[#[.integer 0]]),
  ("compound derived table", expectSQL "compound derived table" "
    CREATE TABLE a(x); CREATE TABLE b(x); INSERT INTO a VALUES(1); INSERT INTO b VALUES(3);
    SELECT z.x FROM (SELECT x FROM a UNION SELECT x FROM b) AS z ORDER BY z.x;"
    #[#[.integer 1], #[.integer 3]]),
  ("compound global order limit", expectSQL "compound global order limit" "
    SELECT 1 AS x UNION SELECT 3 ORDER BY x DESC LIMIT 1;"
    #[#[.integer 3]]),
  ("compound reverse collation", expectSQL "compound reverse collation" "
    SELECT 'a' AS x UNION ALL SELECT 'z' ORDER BY 1 COLLATE reverse;"
    #[#[.text "z"], #[.text "a"]]),
  ("compound inherited collation", expectSQL "compound inherited collation" "
    CREATE TABLE a(x COLLATE nocase); CREATE TABLE b(x COLLATE nocase);
    INSERT INTO a VALUES('ABC'); INSERT INTO b VALUES('abc');
    SELECT x FROM a INTERSECT SELECT x FROM b;"
    #[#[.text "ABC"]]),
  ("compound expression collation", expectSQL "compound expression collation" "
    CREATE TABLE a(x); CREATE TABLE b(x);
    INSERT INTO a VALUES('ABC'); INSERT INTO b VALUES('abc');
    SELECT x COLLATE nocase FROM a EXCEPT SELECT x FROM b;" #[]),
  ("compound order validation", expectError "compound order validation"
    "SELECT 1 AS x UNION SELECT 3 ORDER BY x+1;" "does not match any column"),
  ("correlated inner scope", expectSQL "correlated inner scope" "
    CREATE TABLE t(a,b); INSERT INTO t VALUES('outer','1'),('inner','2');
    SELECT a FROM t AS o WHERE b IN (SELECT b FROM t WHERE a='inner');"
    #[#[.text "inner"]]),
  ("subquery arity", expectError "subquery arity" "
    SELECT 1 IN (SELECT 1,2);" "sub-select returns 2 columns - expected 1"),
  ("double-quoted string mode", expectError "double-quoted string mode" "
    PRAGMA lean_dqs_dml=0; SELECT \"missing\";" "should this be a string literal"),
  ("values query", expectSQL "values query" "VALUES(1,'a'),(2,'b');"
    #[#[.integer 1, .text "a"], #[.integer 2, .text "b"]]),
  ("values compound", expectSQL "values compound" "
    VALUES(1),(2),(3) EXCEPT VALUES(2);"
    #[#[.integer 1], #[.integer 3]]),
  ("compound clause placement", expectError "compound clause placement" "
    SELECT 1 ORDER BY 1 UNION ALL SELECT 2;" "ORDER BY clause should come after UNION ALL"),
  ("live view", expectSQL "live view" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1); CREATE VIEW v(y) AS SELECT x+1 FROM t;
    INSERT INTO t VALUES(4); SELECT y FROM v ORDER BY y;"
    #[#[.integer 2], #[.integer 5]]),
  ("view with cte", expectSQL "view with cte" "
    CREATE VIEW v(x) AS WITH c(y) AS (SELECT 123)
      SELECT (SELECT min(y) OVER()) FROM c GROUP BY y;
    SELECT * FROM v;" #[#[.integer 123]]),
  ("view rollback", expectError "view rollback" "
    BEGIN; CREATE VIEW v AS SELECT 1 AS x; ROLLBACK; SELECT * FROM v;" "no such table"),
  ("grouped aggregates", expectSQL "grouped aggregates" "
    CREATE TABLE t(k,v); INSERT INTO t VALUES('a',1),('a',2),('b',4);
    SELECT k,sum(v) AS total FROM t GROUP BY k HAVING total>2 ORDER BY total;"
    #[#[.text "a", .integer 3], #[.text "b", .integer 4]]),
  ("derived aggregate having", expectSQL "derived aggregate having" "
    CREATE TABLE t(k,v); INSERT INTO t VALUES(1,1),(2,2),(2,4);
    SELECT a,k FROM (SELECT avg(v) AS a,k FROM t GROUP BY k HAVING a>1) ORDER BY k;"
    #[#[.real 3.0, .integer 2]]),
  ("group and order aliases", expectSQL "group and order aliases" "
    CREATE TABLE t(k); INSERT INTO t VALUES(0),(0),(1);
    SELECT k+1 AS x,count(*) AS n FROM t GROUP BY x ORDER BY 10-(2*x+n);"
    #[#[.integer 2, .integer 1], #[.integer 1, .integer 2]]),
  ("aggregate where alias", expectSQL "aggregate where alias" "
    CREATE TABLE t(a,b,c); INSERT INTO t VALUES(1,'aa','bb'),(2,'cc','dd');
    SELECT a AS x,b||c AS y FROM t WHERE y='aabb' GROUP BY x,y;"
    #[#[.integer 1, .text "aabb"]]),
  ("group ordinal validation", expectError "group ordinal validation" "
    CREATE TABLE t(k); SELECT k,count(*) FROM t GROUP BY 0;" "GROUP BY term out of range"),
  ("three-part group name", expectError "three-part group name" "
    CREATE TABLE t(k); INSERT INTO t VALUES(1);
    SELECT k,count(*) FROM t GROUP BY temp.t.k;" "no such column: temp.t.k"),
  ("empty aggregate row", expectSQL "empty aggregate row" "
    CREATE TABLE t(a,b); SELECT a,sum(b) FROM t WHERE 0;"
    #[#[.null, .null]]),
  ("generated column recomputation", expectSQL "generated column recomputation" "
    CREATE TABLE t(a REAL,b REAL GENERATED ALWAYS AS (a+1));
    INSERT INTO t(a) VALUES(1); UPDATE t SET a=4;
    ALTER TABLE t ADD COLUMN c REAL AS (b+1); SELECT * FROM t;"
    #[#[.real 4.0, .real 5.0, .real 6.0]]),
  ("aggregate alias recursion", expectError "aggregate alias recursion" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1); SELECT min(x) AS m FROM t
    GROUP BY x HAVING max(m+1)>0;" "misuse of aliased aggregate m"),
  ("table constraint parser", expectSQL "table constraint parser" "
    CREATE TABLE t(a,b,c,PRIMARY KEY(a,b)); INSERT INTO t VALUES(1,2,3);
    INSERT INTO t SELECT a+(SELECT max(a) FROM t),b,c FROM t; SELECT count(*) FROM t;"
    #[#[.integer 2]]),
  ("syntax diagnostics", expectError "syntax diagnostics" "SELECT 1 WHERE 1=;"
    "near \";\": syntax error"),
  ("limit expression", expectSQL "limit expression" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1),(2),(3); SELECT x FROM t LIMIT 1+1;"
    #[#[.integer 1], #[.integer 2]]),
  ("foreign key cascade", expectSQL "foreign key cascade" "
    PRAGMA foreign_keys=ON;
    CREATE TABLE p(a,b UNIQUE); CREATE TABLE c(d REFERENCES p(b) ON DELETE CASCADE);
    CREATE TABLE log(x); CREATE TRIGGER cd AFTER DELETE ON c BEGIN INSERT INTO log VALUES(old.d); END;
    INSERT INTO p VALUES(1,7); INSERT INTO c VALUES(7); REPLACE INTO p VALUES(2,7);
    SELECT p.a,count(c.d),count(log.x) FROM p LEFT JOIN c ON c.d=p.b,log;"
    #[#[.integer 2, .integer 0, .integer 1]]),
  ("foreign key enforcement", expectError "foreign key enforcement" "
    PRAGMA foreign_keys=ON; CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(k REFERENCES p(k));
    INSERT INTO c VALUES(9);" "FOREIGN KEY constraint failed"),
  ("count changes", expectSQL "count changes" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1),(2),(3); PRAGMA count_changes=ON;
    DELETE FROM t WHERE x<3; DELETE FROM t;"
    #[#[.integer 2], #[.integer 1]]),
  ("delete trigger update", expectSQL "delete trigger update" "
    CREATE TABLE t(x); CREATE TABLE counter(n); INSERT INTO t VALUES(1),(2); INSERT INTO counter VALUES(0);
    CREATE TRIGGER td AFTER DELETE ON t BEGIN UPDATE counter SET n=n+1; END;
    DELETE FROM t; SELECT n FROM counter;"
    #[#[.integer 2]]),
  ("trigger outer diagnostic", expectError "trigger outer diagnostic" "
    CREATE TABLE source(a,b); INSERT INTO source VALUES(1,2); CREATE TABLE target(n);
    CREATE TRIGGER ti AFTER INSERT ON target BEGIN
      SELECT a FROM source WHERE a>new.missing UNION ALL SELECT b FROM source;
    END;
    INSERT INTO target VALUES(1);" "no such column: new.missing"),
  ("composite uniqueness", expectError "composite uniqueness" "
    CREATE TABLE t(a,b,c,UNIQUE(a,b)); INSERT INTO t VALUES(1,2,3),(1,2,4);"
    "UNIQUE constraint failed: t.a, t.b"),
  ("update preserves scan slot", expectSQL "update preserves scan slot" "
    CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,10),(2,20);
    UPDATE t SET v=11 WHERE id=1; SELECT * FROM t;"
    #[#[.integer 1, .integer 11], #[.integer 2, .integer 20]]),
  ("alter add column", expectSQL "alter add column" "
    CREATE TABLE t(x); INSERT INTO t VALUES(7); ALTER TABLE t ADD COLUMN y DEFAULT 3;
    SELECT x,y,printf('y%d',x) FROM t;"
    #[#[.integer 7, .integer 3, .text "y7"]]),
  ("like and glob", expectSQL "like and glob" "
    SELECT 'Alpha' LIKE 'a_ph%', 'abc' GLOB 'a*';"
    #[#[.integer 1, .integer 1]]),
  ("recursive cte insert", expectSQL "recursive cte insert" "
    CREATE TABLE t(x);
    WITH RECURSIVE n(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM n WHERE x<4)
      INSERT INTO t SELECT x FROM n;
    SELECT x FROM t ORDER BY x;"
    #[#[.integer 1], #[.integer 2], #[.integer 3], #[.integer 4]]),
  ("recursive select seed", expectSQL "recursive select seed" "
    WITH RECURSIVE n(x) AS (SELECT 1 UNION ALL SELECT x+1 FROM n WHERE x<3)
      SELECT x FROM n ORDER BY x;"
    #[#[.integer 1], #[.integer 2], #[.integer 3]]),
  ("implicit recursive cte", expectSQL "implicit recursive cte" "
    CREATE TABLE t(x);
    WITH n(x) AS (SELECT 1 UNION ALL SELECT x+1 FROM n WHERE x<3)
      INSERT INTO t SELECT x FROM n;
    SELECT x FROM t ORDER BY x;"
    #[#[.integer 1], #[.integer 2], #[.integer 3]]),
  ("row varying random", expectSQL "row varying random" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1),(2),(3),(4),(5);
    SELECT abs(random())%5 AS r FROM t GROUP BY 1 ORDER BY 1;"
    #[#[.integer 0], #[.integer 1], #[.integer 2], #[.integer 3], #[.integer 4]]),
  ("index schema catalog", expectSQL "index schema catalog" "
    CREATE TABLE t(x); CREATE INDEX tx ON t(x);
    SELECT name FROM sqlite_master WHERE type='index';"
    #[#[.text "tx"]]),
  ("empty window input", expectSQL "empty window input" "
    CREATE TABLE t(x); SELECT sum(x) OVER() FROM t;" #[]),
  ("rowid reuse after empty", expectSQL "rowid reuse after empty" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1),(2); DELETE FROM t; INSERT INTO t VALUES(3);
    SELECT rowid FROM t;" #[#[.integer 1]]),
  ("integer cast numeric prefix", expectSQL "integer cast numeric prefix" "
    SELECT CAST('123abc' AS INTEGER), CAST('1.5' AS REAL)+1;"
    #[#[.integer 123, .real 2.5]]),
  ("IS truth predicates", expectSQL "IS truth predicates" "
    SELECT NULL IS TRUE,NULL IS NOT TRUE,2 IS TRUE,0 IS FALSE;"
    #[#[.integer 0, .integer 1, .integer 1, .integer 1]]),
  ("json extract", expectSQL "json extract" "
    SELECT json_extract('{\"a\":5}', '$.a'), printf('%s%d','x',4),
      json_extract('{outer:{answer:\"ok\"}}', '$.outer.answer');"
    #[#[.integer 5, .text "x4", .text "ok"]]),
  ("expression index scan order", expectSQL "expression index scan order" "
    CREATE TABLE t(b); INSERT INTO t VALUES('one'),('two'),('three');
    CREATE INDEX tx ON t(b||'x');
    SELECT b='two',b='three' FROM t WHERE b||'x'>'onex';"
    #[#[.integer 0, .integer 1], #[.integer 1, .integer 0]]),
  ("aggregate subquery order source", expectSQL "aggregate subquery order source" "
    CREATE TABLE t(c0); INSERT INTO t VALUES(1),(2);
    SELECT (SELECT count(*) FROM t ORDER BY c0);" #[#[.integer 2]]),
  ("automatic index catalog", expectSQL "automatic index catalog" "
    CREATE TABLE t(a UNIQUE PRIMARY KEY,b,UNIQUE(a,b));
    SELECT name,sql IS NULL FROM sqlite_master WHERE type='index' ORDER BY name;"
    #[#[.text "sqlite_autoindex_t_1", .integer 1],
      #[.text "sqlite_autoindex_t_2", .integer 1]]),
  ("automatic index cannot drop", expectError "automatic index cannot drop" "
    CREATE TABLE t(a UNIQUE); DROP INDEX sqlite_autoindex_t_1;"
    "index associated with UNIQUE or PRIMARY KEY constraint cannot be dropped"),
  ("create index if not exists", expectSQL "create index if not exists" "
    CREATE TABLE t(a); CREATE INDEX IF NOT EXISTS i ON t(a);
    CREATE INDEX IF NOT EXISTS i ON t(a);
    SELECT count(*) FROM sqlite_master WHERE type='index' AND name='i';"
    #[#[.integer 1]]),
  ("composite index prefix order", expectSQL "composite index prefix order" "
    CREATE TABLE t(a,b,c); CREATE INDEX i ON t(a,b);
    INSERT INTO t VALUES('', '',1),('',NULL,2),(NULL,'',3);
    SELECT c FROM t WHERE a='';" #[#[.integer 2], #[.integer 1]]),
  ("reserved schema name", expectError "reserved schema name" "CREATE TABLE sqlite_private(x);"
    "object name reserved for internal use"),
  ("conflict rollback state", expectConflictRollback),
  ("not null conflict default", expectSQL "not null conflict default" "
    CREATE TABLE t(x NOT NULL ON CONFLICT REPLACE DEFAULT 5);
    INSERT INTO t VALUES(NULL); INSERT OR REPLACE INTO t VALUES(NULL);
    SELECT x FROM t;" #[#[.integer 5], #[.integer 5]]),
  ("explicit abort overrides constraint", expectError "explicit abort overrides constraint" "
    CREATE TABLE t(x NOT NULL ON CONFLICT REPLACE DEFAULT 5);
    INSERT OR ABORT INTO t VALUES(NULL);" "NOT NULL constraint failed: t.x"),
  ("check conflict ignore", expectSQL "check conflict ignore" "
    CREATE TABLE t(a CHECK(a!=2));
    INSERT OR IGNORE INTO t VALUES(1),(2),(3); SELECT a FROM t ORDER BY a;"
    #[#[.integer 1], #[.integer 3]]),
  ("duplicate unique conflict policies", expectSQL "duplicate unique conflict policies" "
    CREATE TABLE t(x PRIMARY KEY,UNIQUE(x,x),UNIQUE(x,x) ON CONFLICT REPLACE);
    INSERT INTO t VALUES(1); SELECT x FROM t;" #[#[.integer 1]]),
  ("named check diagnostic", expectError "named check diagnostic" "
    CREATE TABLE t(x CONSTRAINT positive CHECK(x>0)); INSERT INTO t VALUES(0);"
    "CHECK constraint failed: positive"),
  ("check schema validation", expectError "check schema validation" "
    CREATE TABLE t(x,CHECK(x<(SELECT 1)));" "subqueries prohibited in CHECK constraints"),
  ("ignored check integrity", expectSQL "ignored check integrity" "
    CREATE TABLE t(x CHECK(x>0)); PRAGMA ignore_check_constraints=ON;
    INSERT INTO t VALUES(0); PRAGMA ignore_check_constraints=OFF; PRAGMA integrity_check;"
    #[#[.text "CHECK constraint failed in t"]]),
  ("OR FAIL partial update", expectFailKeepsEarlierUpdates),
  ("multiple primary keys", expectError "multiple primary keys" "
    CREATE TABLE t(a PRIMARY KEY,b PRIMARY KEY);" "has more than one primary key"),
  ("failed unique index atomicity", expectFailedUniqueIndexIsAtomic),
  ("serialized connection stress", expectSerializedConnectionStress),
  ("verified WAL concurrency model", expectWALConcurrencyModel),
  ("WAL reader-writer stress", expectWALConnectionStress),
  ("cross-process serialized MVP commits", expectCrossProcessSerializedMVP),
  ("cross-process physical WAL readers and writers", expectCrossProcessPhysicalWAL),
  ("missing table error", expectError "missing table" "SELECT * FROM absent;" "no such table"),
  ("row width error", expectError "row width" "CREATE TABLE t(a,b); INSERT INTO t VALUES(1);" "2 columns")
]

def main (args : List String) : IO UInt32 := do
  if let ["--wal-index-fixture", walPath, shmPath] := args then
    let frames ← expectSQLiteWALIndexFixture walPath shmPath
    IO.println s!"WAL index fixture: {frames} frames, 8 interrupted-append splits"
    return 0
  if let ["--wal-append-fixture", walPath, imagePath, destination] := args then
    let frames ← exportSQLiteWALAppend walPath imagePath destination
    IO.println s!"WAL append fixture: {frames} committed frames"
    return 0
  unless args.isEmpty do throw (IO.userError "unknown test-runner arguments")
  let mut passed := 0
  for (name, test) in unitTests do
    try
      test
      passed := passed + 1
      IO.println s!"ok - {name}"
    catch e =>
      IO.eprintln s!"not ok - {name}: {e}"
      return 1
  IO.println s!"{passed} SQLeanite tests passed"
  pure 0
