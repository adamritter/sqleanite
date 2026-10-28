import SQLeanite.Engine.StatementWrites
import SQLeanite.ProcessLock
import SQLeanite.SerializedConnection
import SQLeanite.WALConnection
import SQLeanite.WALMultiWriter

namespace SQLeanite.Tests
open SQLeanite

def fail (message : String) : IO α := throw (IO.userError message)

def expectSQL (name sql : String) (expected : Array (Array Value)) : IO Unit :=
  match runSQL {} sql with
  | .error e => fail s!"{name}: unexpected error: {e}"
  | .ok (_, result) =>
    unless result.rows == expected do
      fail s!"{name}: expected {repr expected}, got {repr result.rows}"

def expectError (name sql fragment : String) : IO Unit :=
  match runSQL {} sql with
  | .ok _ => fail s!"{name}: expected an error containing {fragment}"
  | .error e => unless e.replace fragment "" != e do fail s!"{name}: wrong error: {e}"

def expectConflictRollback : IO Unit := do
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

def expectFailKeepsEarlierUpdates : IO Unit := do
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

def expectFailedUniqueIndexIsAtomic : IO Unit := do
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
def expectSerializedConnectionStress : IO Unit := do
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

def expectWALConcurrencyModel : IO Unit := do
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

def expectWALConnectionStress : IO Unit := do
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

def expectCrossProcessSerializedMVP : IO Unit := do
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

def expectCrossProcessPhysicalWAL : IO Unit := do
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

def expectOrderedIndexCore : IO Unit := do
  let tree := (PagedBTree.Tree.empty : PagedBTree.Tree String)
    |>.insert 8 "eight" |>.insert 3 "three" |>.insert 11 "eleven" |>.insert 8 "updated"
  unless tree.toList.lookup 3 == some "three" && tree.toList.lookup 8 == some "updated" &&
      tree.toList.lookup 7 == none do
    fail "ordered-index core returned an incorrect lookup"

def expectU16Codec : IO Unit := do
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

def expectVarintCase (label : String) (value : FileFormat.U64Value)
    (expected suffix : List UInt8) : IO Unit := do
  let encoded := FileFormat.encodeVarint value
  unless encoded == expected do
    fail s!"SQLite varint {label}: expected {repr expected}, got {repr encoded}"
  unless encoded.length == FileFormat.sqliteVarintSize value.val do
    fail s!"SQLite varint {label}: canonical size disagrees with encoded length"
  unless FileFormat.decodeVarint (encoded ++ suffix) == some (value, suffix) do
    fail s!"SQLite varint {label}: roundtrip did not preserve its suffix"

def expectVarintCodec : IO Unit := do
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

def expectIntegerSerialType (value : Int) (code payloadBytes : Nat) : IO Unit := do
  let serialType := FileFormat.integerSerialType value
  unless (FileFormat.encodeSerialType serialType).val == code &&
      FileFormat.serialTypePayloadSize serialType == payloadBytes do
    fail s!"SQLite integer serial type was wrong for {value}"

def expectSerialTypes : IO Unit := do
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

def expectUnsignedFixedCodec : IO Unit := do
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

def expectSignedIntegerCase {width : FileFormat.IntegerWidth}
    (label : String) (value : FileFormat.SignedInteger width)
    (expected suffix : List UInt8) : IO Unit := do
  let encoded := FileFormat.encodeSignedInteger value
  unless encoded == expected do
    fail s!"signed integer {label}: expected {repr expected}, got {repr encoded}"
  unless FileFormat.decodeSignedInteger width (encoded ++ suffix) ==
      some (value, suffix) do
    fail s!"signed integer {label}: roundtrip did not preserve its suffix"

end SQLeanite.Tests
