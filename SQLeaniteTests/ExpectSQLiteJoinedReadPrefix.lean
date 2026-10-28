import SQLeaniteTests.ExpectSQLiteBetweenConstants
import SQLeaniteTests.ExpectSQLiteJoinedFixedColumns

namespace SQLeanite.Tests
open SQLeanite

def expectSQLiteJoinedReadPrefix : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY,k INTEGER);INSERT INTO l VALUES(1,1),(2,2),(3,-9223372036854775808);INSERT INTO r VALUES(1,1),(2,2),(3,3);"
  let (state, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  let cases : List (String × Bool × List (List Value)) := [
    ("SELECT abs(a.k),a.id,b.id FROM l a JOIN r b ON a.id=b.id;",true,[[.integer 1,.integer 1,.integer 1],[.integer 2,.integer 2,.integer 2]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a JOIN r b ON a.id=b.id ORDER BY a.id;",true,[[.integer 1,.integer 1,.integer 1],[.integer 2,.integer 2,.integer 2]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a JOIN r b ON a.id=b.id ORDER BY a.id DESC LIMIT 1 OFFSET 1;",false,[[.integer 2,.integer 2,.integer 2]]),
    ("SELECT a.id,b.id FROM l a FULL JOIN r b ON abs(a.k)=b.k;",true,[[.integer 1,.integer 1],[.integer 2,.integer 2]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON abs(a.k)=b.k LIMIT 1;",false,[[.integer 1,.integer 1]]),
    ("SELECT a.id,b.id FROM l a JOIN r b ON a.id=b.k+1;",false,[[.integer 2,.integer 1],[.integer 3,.integer 2]]),
    ("SELECT not_a_function(a.k) FROM l a JOIN r b ON a.id=b.id LIMIT 0;",true,[])]
  for (sql, expectedError, values) in cases do
    let statements ← match CoreTokenGrammar.parseStatements sql with
      | .ok result => pure result
      | .error message => fail message
    let [.select query] := statements.toList | fail "joined prefix fixture was not a SELECT"
    let some report := CoreSQL.observeJoinedSelect? state query | fail "joined read observation was missing"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless report.execution.result.rows == expected && report.error.isSome == expectedError do
      fail s!"joined emitted prefix or status differs: {sql}"
    unless report.toExcept.isOk == (CoreSQL.executeSelect state query).isOk do
      fail "joined observation changed ordinary success/error status"
  let script := "SELECT 7;SELECT abs(a.k),a.id,b.id FROM l a JOIN r b ON a.id=b.id;SELECT 9;"
  let expected ← match ([[.integer 7],[.integer 1,.integer 1,.integer 1],[.integer 2,.integer 2,.integer 2]] : List (List Value)).mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-joined-prefix.db"
    journal := ".lake/build/sqleanite-joined-prefix.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  let connection ← CoreFileEngine.create .system paths
  if !(← CoreFileEngine.execute connection setup).isOk then fail "joined prefix file setup"
  let before ← IO.FS.readBinFile paths.main
  let emitted ← IO.mkRef ([] : List (List Core.Value))
  let observe := fun (results : List Core.Result) => emitted.modify (fun rows => rows ++ results.flatMap (·.rows))
  if (← CoreFileEngine.executeObserved connection script observe).isOk then fail "joined file overflow was lost"
  unless (← emitted.get) == expected do fail "joined file lost or duplicated the emitted prefix"
  unless (← IO.FS.readBinFile paths.main) == before do fail "failed joined read changed main bytes"
  let wal : CoreWALFileAdapter.Paths := {
    main := ".lake/build/sqleanite-joined-prefix-wal.db"
    wal := ".lake/build/sqleanite-joined-prefix-wal.db-wal" }
  if ← wal.wal.pathExists then IO.FS.removeFile wal.wal
  if ← wal.main.pathExists then IO.FS.removeFile wal.main
  CoreWALFileAdapter.create .system wal Core.Database.empty
  if !(← CoreWALFileEngine.execute .system wal setup).isOk then fail "joined prefix WAL setup"
  let beforeMain ← IO.FS.readBinFile wal.main
  let beforeWal ← IO.FS.readBinFile wal.wal
  emitted.set []
  if (← CoreWALFileEngine.executeObserved .system wal script observe).isOk then fail "joined WAL overflow was lost"
  unless (← emitted.get) == expected do fail "joined WAL lost or duplicated the emitted prefix"
  unless (← IO.FS.readBinFile wal.main) == beforeMain && (← IO.FS.readBinFile wal.wal) == beforeWal do
    fail "failed joined read changed main/WAL bytes"

def expectSQLiteSingleReadPrefixFiles : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,k INTEGER);INSERT INTO t VALUES(1,0),(2,1),(3,-9223372036854775808);"
  let script := "SELECT 7;\nSELECT id,abs(k) FROM t;\nSELECT 9;\n"
  let expected ← match ([[.integer 7],[.integer 1,.integer 0],[.integer 2,.integer 1]] : List (List Value)).mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-single-prefix.db"
    journal := ".lake/build/sqleanite-single-prefix.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  let connection ← CoreFileEngine.create .system paths
  if !(← CoreFileEngine.execute connection setup).isOk then fail "single-source prefix file setup"
  let before ← IO.FS.readBinFile paths.main
  let emitted ← IO.mkRef ([] : List (List Core.Value))
  let observe := fun (results : List Core.Result) => emitted.modify (fun rows => rows ++ results.flatMap (·.rows))
  if (← CoreFileEngine.executeObserved connection script observe).isOk then fail "single-source file overflow was lost"
  unless (← emitted.get) == expected do fail "single-source file lost or duplicated the emitted prefix"
  unless (← IO.FS.readBinFile paths.main) == before do fail "failed single-source read changed main bytes"
  let wal : CoreWALFileAdapter.Paths := {
    main := ".lake/build/sqleanite-single-prefix-wal.db"
    wal := ".lake/build/sqleanite-single-prefix-wal.db-wal" }
  if ← wal.wal.pathExists then IO.FS.removeFile wal.wal
  if ← wal.main.pathExists then IO.FS.removeFile wal.main
  CoreWALFileAdapter.create .system wal Core.Database.empty
  if !(← CoreWALFileEngine.execute .system wal setup).isOk then fail "single-source prefix WAL setup"
  let beforeMain ← IO.FS.readBinFile wal.main
  let beforeWal ← IO.FS.readBinFile wal.wal
  emitted.set []
  if (← CoreWALFileEngine.executeObserved .system wal script observe).isOk then fail "single-source WAL overflow was lost"
  unless (← emitted.get) == expected do fail "single-source WAL lost or duplicated the emitted prefix"
  unless (← IO.FS.readBinFile wal.main) == beforeMain && (← IO.FS.readBinFile wal.wal) == beforeWal do
    fail "failed single-source read changed main/WAL bytes"

def expectSQLiteJoinEvaluationOrder : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY,k INTEGER);INSERT INTO l VALUES(1,-9223372036854775808);INSERT INTO r VALUES(1,1);INSERT INTO l VALUES(2,2);INSERT INTO r VALUES(2,2);INSERT INTO l VALUES(3,3);INSERT INTO r VALUES(3,3);INSERT INTO l VALUES(4,4);INSERT INTO r VALUES(4,4);"
  let cases : List (String × List (List Value)) := [
    ("SELECT abs(a.k),a.id,b.id FROM l a JOIN r b ON a.id=b.id ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a JOIN r b ON a.id=b.id ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 3]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a JOIN r b ON a.id+0=b.id ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a JOIN r b ON a.id+0=b.id ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 3]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a JOIN r b ON abs(a.k)=b.k WHERE a.id>1;",[[.integer 2,.integer 2,.integer 2],[.integer 3,.integer 3,.integer 3],[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 3]]),
    ("SELECT a.id,b.id FROM l a JOIN r b ON abs(a.k)=b.k WHERE a.id>1;",[[.integer 2,.integer 2],[.integer 3,.integer 3],[.integer 4,.integer 4]]),
    ("SELECT a.id,b.id FROM l a JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4]]),
    ("SELECT a.id,b.id FROM l a JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3]]),
    ("SELECT count(*) FROM l a JOIN r b ON abs(a.k)=b.k WHERE a.id>1;",[[.integer 3]]),
    ("SELECT count(*) FROM l a JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 3]]),
    ("SELECT count(*) FROM l a JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[]),
    ("SELECT abs(a.k),a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 3]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a LEFT JOIN r b ON a.id+0=b.id ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a LEFT JOIN r b ON a.id+0=b.id ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 3]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a LEFT JOIN r b ON abs(a.k)=b.k WHERE a.id>1;",[[.integer 2,.integer 2,.integer 2],[.integer 3,.integer 3,.integer 3],[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a LEFT JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a LEFT JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 3]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON abs(a.k)=b.k WHERE a.id>1;",[[.integer 2,.integer 2],[.integer 3,.integer 3],[.integer 4,.integer 4]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3]]),
    ("SELECT count(*) FROM l a LEFT JOIN r b ON abs(a.k)=b.k WHERE a.id>1;",[[.integer 3]]),
    ("SELECT count(*) FROM l a LEFT JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 3]]),
    ("SELECT count(*) FROM l a LEFT JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[]),
    ("SELECT abs(a.k),a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.k+1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 3]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.k+1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 2]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a RIGHT JOIN r b ON a.id=b.id ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a RIGHT JOIN r b ON a.id=b.id ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 3]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a RIGHT JOIN r b ON a.id+0=b.id ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a RIGHT JOIN r b ON a.id+0=b.id ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 3]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a RIGHT JOIN r b ON abs(a.k)=b.k WHERE a.id>1;",[[.integer 2,.integer 2,.integer 2],[.integer 3,.integer 3,.integer 3],[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a RIGHT JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a RIGHT JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 3]]),
    ("SELECT a.id,b.id FROM l a RIGHT JOIN r b ON abs(a.k)=b.k WHERE a.id>1;",[[.integer 2,.integer 2],[.integer 3,.integer 3],[.integer 4,.integer 4]]),
    ("SELECT a.id,b.id FROM l a RIGHT JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4]]),
    ("SELECT a.id,b.id FROM l a RIGHT JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3]]),
    ("SELECT count(*) FROM l a RIGHT JOIN r b ON abs(a.k)=b.k WHERE a.id>1;",[[.integer 3]]),
    ("SELECT count(*) FROM l a RIGHT JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 3]]),
    ("SELECT count(*) FROM l a RIGHT JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[]),
    ("SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id=b.id ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id=b.id ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 3]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id+0=b.id ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id+0=b.id ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 3]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON abs(a.k)=b.k WHERE a.id>1;",[[.integer 2,.integer 2,.integer 2],[.integer 3,.integer 3,.integer 3],[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 4]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 3]]),
    ("SELECT a.id,b.id FROM l a FULL JOIN r b ON abs(a.k)=b.k WHERE a.id>1;",[[.integer 2,.integer 2],[.integer 3,.integer 3],[.integer 4,.integer 4]]),
    ("SELECT a.id,b.id FROM l a FULL JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4]]),
    ("SELECT a.id,b.id FROM l a FULL JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3]]),
    ("SELECT count(*) FROM l a FULL JOIN r b ON abs(a.k)=b.k WHERE a.id>1;",[[.integer 3]]),
    ("SELECT count(*) FROM l a FULL JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 3]]),
    ("SELECT count(*) FROM l a FULL JOIN r b ON abs(a.k)=b.k WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[]),
    ("SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id=b.k+1 ORDER BY a.id DESC,b.id LIMIT 1;",[[.integer 4,.integer 4,.integer 3]]),
    ("SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id=b.k+1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1;",[[.integer 3,.integer 3,.integer 2]])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"joined evaluation order: {sql}: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"joined evaluation order or early filter: {sql}"
  for sql in ["SELECT a.id,b.id FROM l a FULL JOIN r b ON abs(a.k)=b.k WHERE a.k IS NULL;",
    "SELECT a.id,b.id FROM l a FULL JOIN r b ON abs(a.k)=b.k WHERE coalesce(a.k,0)>1;",
    "SELECT a.id,b.id FROM l a FULL JOIN r b ON abs(a.k)=b.k WHERE a.id>1 OR b.id>1;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"joined WHERE incorrectly removed a required ON evaluation: {sql}"

  let offsetCases : List (String × List (List Value)) := [
    ("CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY,k INTEGER);INSERT INTO l VALUES(1,-9223372036854775808);INSERT INTO r VALUES(1,1);INSERT INTO l VALUES(2,2);INSERT INTO r VALUES(2,2);INSERT INTO l VALUES(3,3);INSERT INTO r VALUES(3,3);INSERT INTO l VALUES(4,4);INSERT INTO r VALUES(4,4);SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id+0=b.id WHERE a.id<4 ORDER BY a.id ASC,b.id LIMIT 4 OFFSET 2;",[[.integer 3,.integer 3,.integer 3]]),
    ("CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY,k INTEGER);INSERT INTO l VALUES(1,3);INSERT INTO r VALUES(1,-5);INSERT INTO l VALUES(2,4);INSERT INTO r VALUES(2,5);INSERT INTO l VALUES(3,-9223372036854775808);INSERT INTO r VALUES(3,4);INSERT INTO l VALUES(4,-5);INSERT INTO r VALUES(4,5);SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id=b.k+1 WHERE a.id>1 ORDER BY a.id ASC,b.id LIMIT 3 OFFSET 2;",[[.integer 5,.integer 4,.null]]),
    ("CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY,k INTEGER);INSERT INTO l VALUES(1,3);INSERT INTO r VALUES(1,-5);INSERT INTO l VALUES(2,4);INSERT INTO r VALUES(2,5);INSERT INTO l VALUES(3,-9223372036854775808);INSERT INTO r VALUES(3,4);INSERT INTO l VALUES(4,-5);INSERT INTO r VALUES(4,5);SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id=b.id WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 3;",[]),
    ("CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY,k INTEGER);INSERT INTO l VALUES(1,2);INSERT INTO r VALUES(1,-3);INSERT INTO l VALUES(2,-5);INSERT INTO r VALUES(2,0);INSERT INTO l VALUES(3,-9223372036854775808);INSERT INTO r VALUES(3,-4);INSERT INTO l VALUES(4,5);INSERT INTO r VALUES(4,0);SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id=b.k+1 WHERE a.id>1 ORDER BY a.id ASC,b.id LIMIT 3 OFFSET 2;",[[.integer 5,.integer 4,.null]]),
    ("CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY,k INTEGER);INSERT INTO l VALUES(1,2);INSERT INTO r VALUES(1,-3);INSERT INTO l VALUES(2,-5);INSERT INTO r VALUES(2,0);INSERT INTO l VALUES(3,-9223372036854775808);INSERT INTO r VALUES(3,-4);INSERT INTO l VALUES(4,5);INSERT INTO r VALUES(4,0);SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id=b.id WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 3;",[]),
    ("CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY,k INTEGER);INSERT INTO l VALUES(1,3);INSERT INTO r VALUES(1,-5);INSERT INTO l VALUES(2,-5);INSERT INTO r VALUES(2,2);INSERT INTO l VALUES(3,-9223372036854775808);INSERT INTO r VALUES(3,-2);INSERT INTO l VALUES(4,-4);INSERT INTO r VALUES(4,3);SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id=b.k+1 WHERE a.id>1 ORDER BY a.id ASC,b.id LIMIT 3 OFFSET 2;",[[.integer 4,.integer 4,.integer 4]]),
    ("CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY,k INTEGER);INSERT INTO l VALUES(1,3);INSERT INTO r VALUES(1,-5);INSERT INTO l VALUES(2,-5);INSERT INTO r VALUES(2,2);INSERT INTO l VALUES(3,-9223372036854775808);INSERT INTO r VALUES(3,-2);INSERT INTO l VALUES(4,-4);INSERT INTO r VALUES(4,3);SELECT abs(a.k),a.id,b.id FROM l a FULL JOIN r b ON a.id=b.id WHERE a.id>1 ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 3;",[])]
  for (sql, values) in offsetCases do
    let (_, output) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"joined scan OFFSET: {sql}: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"joined scan OFFSET evaluated a skipped projection: {sql}"

def expectSQLiteJoinedExpressions : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k TEXT);CREATE TABLE r(id INTEGER PRIMARY KEY,k NUMERIC);INSERT INTO l VALUES(1,'01'),(2,'A'),(3,NULL);INSERT INTO r VALUES(1,1),(2,'a'),(4,2);"
  let cases : List (String × List (List Value)) := [
    ("SELECT a.id AS lid,b.id AS rid,a.k+b.k AS added,coalesce(a.k,b.k) AS chosen FROM l a FULL JOIN r b ON a.id=b.id ORDER BY a.id,b.id;", [[.null,.integer 4,.null,.integer 2],[.integer 1,.integer 1,.integer 2,.text "01"],[.integer 2,.integer 2,.integer 0,.text "A"],[.integer 3,.null,.null,.null]]),
    ("SELECT a.id AS lid,b.id AS rid,typeof(k) AS kind,k+1 AS added FROM l a FULL JOIN r b USING(k) ORDER BY a.id,b.id;", [[.null,.integer 2,.text "text",.integer 1],[.null,.integer 4,.text "integer",.integer 3],[.integer 1,.integer 1,.text "text",.integer 2],[.integer 2,.null,.text "text",.integer 1],[.integer 3,.null,.text "null",.null]]),
    ("SELECT upper(a.k) AS chosen,a.id AS lid,b.id AS rid FROM l a JOIN r b ON a.id=b.id WHERE chosen='A' ORDER BY chosen;", [[.text "A",.integer 2,.integer 2]]),
    ("SELECT a.id AS lid,b.id AS rid FROM l a FULL JOIN r b ON a.id+1=b.id ORDER BY a.id,b.id;", [[.null,.integer 1],[.integer 1,.integer 2],[.integer 2,.null],[.integer 3,.integer 4]]),
    ("SELECT a.id AS lid,b.id AS rid FROM l a FULL JOIN r b ON coalesce(a.k,0)=b.k WHERE b.id IS NOT NULL ORDER BY a.id,b.id;", [[.null,.integer 2],[.null,.integer 4],[.integer 1,.integer 1]]),
    ("SELECT count(*) AS n,count(a.k) AS filled,sum(b.k) AS total FROM l a FULL JOIN r b ON a.id=b.id;", [[.integer 4,.integer 2,.real 3.0]]),
    ("SELECT a.k AS key,count(*) AS n FROM l a FULL JOIN r b ON a.id=b.id GROUP BY a.k ORDER BY a.k;", [[.null,.integer 2],[.text "01",.integer 1],[.text "A",.integer 1]]),
    ("SELECT coalesce(a.k,b.k) AS chosen,a.id AS lid,b.id AS rid FROM l a FULL JOIN r b ON a.id=b.id ORDER BY chosen,a.id,b.id LIMIT 2 OFFSET 1;", [[.integer 2,.null,.integer 4],[.text "01",.integer 1,.integer 1]]),
    ("SELECT DISTINCT lower(a.k) AS chosen FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY chosen;", [[.null],[.text "01"],[.text "a"]]),
    ("SELECT a.k+1 AS chosen FROM l a JOIN r b ON a.id=b.id UNION ALL SELECT 9 ORDER BY chosen;", [[.integer 1],[.integer 2],[.integer 9]]),
    ("SELECT min(a.k,b.k COLLATE missing) AS chosen FROM l a JOIN r b ON a.id=b.id LIMIT 0;", [])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"joined expression/collation: {sql}: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"joined expression value, binding, affinity or function collation: {sql}"
  for sql in ["CREATE TABLE Extra AS SELECT min(a.k,b.k COLLATE missing) AS chosen FROM l a JOIN r b ON a.id=b.id LIMIT 0;","SELECT not_a_function(a.k) FROM l a JOIN r b ON a.id=b.id LIMIT 0;","SELECT a.missing+1 FROM l a JOIN r b ON a.id=b.id LIMIT 0;","SELECT likely(a.k)+1 FROM l a JOIN r b ON a.id=b.id ORDER BY missing LIMIT 0;","SELECT a.k AS chosen,b.k AS next FROM l a JOIN r b ON a.id=b.id WHERE a.chosen+1;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"joined expression or scalar collation omitted required validation: {sql}"

def expectSQLiteFunctionArgumentCollations : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,a TEXT,b TEXT);INSERT INTO t VALUES(1,'A','a'),(2,'z ','z');"
  let cases : List (String × List (List Value)) := [
    ("SELECT min(a,b COLLATE nocase) AS lo,max(a,b COLLATE nocase) AS hi,nullif(a,b COLLATE nocase) AS unequal FROM t ORDER BY id;", [[.text "A",.text "a",.text "A"],[.text "z",.text "z ",.text "z "]]),
    ("SELECT min(+a,b COLLATE nocase) AS plus,min(likely(a),b COLLATE nocase) AS hinted,min(CAST(a AS TEXT),b COLLATE nocase) AS casted FROM t ORDER BY id;", [[.text "A",.text "a",.text "A"],[.text "z",.text "z",.text "z"]]),
    ("SELECT min(a,b COLLATE missing) AS lo,max(a,b COLLATE missing) AS hi,nullif(a,b COLLATE missing) AS unequal FROM t ORDER BY id;", [[.text "A",.text "a",.text "A"],[.text "z",.text "z ",.text "z "]]),
    ("SELECT min(a COLLATE rtrim,b COLLATE missing) AS lo FROM t ORDER BY id;", [[.text "A"],[.text "z"]]),
    ("SELECT min(a,b COLLATE missing) FROM t LIMIT 0;", [])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"joined expression/collation: {sql}: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"joined expression value, binding, affinity or function collation: {sql}"
  for sql in ["SELECT min(likely(a),b COLLATE missing) FROM t LIMIT 0;","SELECT min(a+0,b COLLATE missing) FROM t LIMIT 0;","SELECT min(a,b COLLATE missing)='A' FROM t LIMIT 0;","SELECT min(a,b COLLATE missing) FROM t ORDER BY 1 LIMIT 0;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"joined expression or scalar collation omitted required validation: {sql}"

def expectSQLiteJoinCompoundBinding : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k TEXT);CREATE TABLE r(id INTEGER PRIMARY KEY,k NUMERIC);INSERT INTO l VALUES(1,'a'),(2,'z');INSERT INTO r VALUES(1,'b'),(3,'c');"
  let cases : List (String × List (List Value)) := [
    ("SELECT * FROM l a JOIN r b USING(id) UNION ALL SELECT 9,8,7 ORDER BY k;",
      [[.integer 9,.integer 8,.integer 7],[.integer 1,.text "a",.text "b"]]),
    ("SELECT * FROM l a LEFT JOIN r b USING(id) UNION ALL SELECT 9,8,7 ORDER BY b.k;",
      [[.integer 2,.text "z",.null],[.integer 9,.integer 8,.integer 7],[.integer 1,.text "a",.text "b"]]),
    ("SELECT * FROM l a FULL JOIN r b USING(id) UNION ALL SELECT 9,8,7 ORDER BY b.k;",
      [[.integer 2,.text "z",.null],[.integer 9,.integer 8,.integer 7],
       [.integer 1,.text "a",.text "b"],[.integer 3,.null,.text "c"]]),
    ("SELECT a.* FROM l a RIGHT JOIN r b USING(id) UNION ALL SELECT 9,8 ORDER BY b.id;",
      [[.integer 1,.text "a"],[.integer 3,.null],[.integer 9,.integer 8]]),
    ("SELECT id FROM l a FULL JOIN r b USING(id) UNION ALL SELECT 9 ORDER BY id;",
      [[.integer 1],[.integer 2],[.integer 3],[.integer 9]]),
    ("SELECT a.k AS chosen,b.k AS chosen FROM l a JOIN r b USING(id) UNION ALL SELECT 9,8 ORDER BY chosen;",
      [[.integer 9,.integer 8],[.text "a",.text "b"]]),
    ("SELECT * FROM l a FULL JOIN r b USING(id) INTERSECT SELECT * FROM l a FULL JOIN r b USING(id) ORDER BY b.k;",
      [[.integer 2,.text "z",.null],[.integer 1,.text "a",.text "b"],[.integer 3,.null,.text "c"]]),
    ("SELECT * FROM l a NATURAL FULL JOIN r b UNION ALL SELECT 9,8 ORDER BY k;",
      [[.integer 9,.integer 8],[.integer 1,.text "a"],[.integer 1,.text "b"],
       [.integer 3,.text "c"],[.integer 2,.text "z"]]),
    ("CREATE TABLE Extra AS SELECT * FROM l a FULL JOIN r b USING(id) UNION ALL SELECT 9,8,7 ORDER BY b.k;SELECT rowid,* FROM Extra ORDER BY rowid;",
      [[.integer 1,.integer 2,.text "z",.null],[.integer 2,.integer 9,.integer 8,.integer 7],
       [.integer 3,.integer 1,.text "a",.text "b"],[.integer 4,.integer 3,.null,.text "c"]])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"joined compound result binding: {sql}: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"joined compound result slots, names or source identity: {sql}"
  for sql in [
      "SELECT a.* FROM l a RIGHT JOIN r b USING(id) UNION ALL SELECT 1,2 ORDER BY a.id;",
      "SELECT a.* FROM l a FULL JOIN r b USING(id) UNION ALL SELECT 1,2 ORDER BY a.id;",
      "SELECT a.* FROM l a FULL JOIN r b USING(id) UNION ALL SELECT 1,2 ORDER BY b.id;",
      "SELECT a.* FROM l a FULL JOIN r b USING(id) UNION ALL SELECT 1,2 ORDER BY coalesce(a.id,b.id);",
      "SELECT a.id FROM l a RIGHT JOIN r b USING(id) UNION ALL SELECT 1 ORDER BY id;",
      "SELECT * FROM l a JOIN r b USING(id) UNION ALL SELECT 1,2,3 ORDER BY 4;",
      "SELECT a.k FROM l a JOIN r b ON a.id=b.id UNION ALL SELECT 1 ORDER BY k;",
      "SELECT a.* FROM l a FULL JOIN r b USING(id) UNION ALL SELECT 1,2 ORDER BY id COLLATE missing LIMIT 0;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"compound ordering lost source identity, width, ambiguity or collation validation: {sql}"

def expectSQLiteJoinAliases : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k TEXT);CREATE TABLE r(id INTEGER PRIMARY KEY,k NUMERIC);INSERT INTO l VALUES(1,'01'),(2,'A'),(3,NULL);INSERT INTO r VALUES(1,1),(2,'a'),(4,2);"
  let cases : List (String × List (List Value)) := [
    ("SELECT b.k AS chosen,a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE chosen='01' ORDER BY a.id,b.id;",
      [[.integer 1,.integer 1,.integer 1]]),
    ("SELECT likely(b.k) AS chosen,a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE chosen='01' ORDER BY a.id,b.id;", []),
    ("SELECT a.k COLLATE nocase AS chosen,a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE chosen='a' ORDER BY a.id,b.id;",
      [[.text "A",.integer 2,.integer 2]]),
    ("SELECT a.k COLLATE nocase AS chosen,a.id,b.id FROM l a LEFT JOIN r b ON chosen=b.k ORDER BY a.id,b.id;",
      [[.text "01",.integer 1,.integer 1],[.text "A",.integer 2,.integer 2],[.null,.integer 3,.null]]),
    ("SELECT k AS chosen,a.id,b.id FROM l a FULL JOIN r b USING(k) WHERE chosen=2 ORDER BY a.id,b.id;",
      [[.integer 2,.null,.integer 4]]),
    ("SELECT a.k COLLATE nocase AS chosen FROM l a LEFT JOIN r b ON a.id=b.id WHERE chosen IS NOT NULL ORDER BY chosen DESC;",
      [[.text "A"],[.text "01"]]),
    ("SELECT b.k AS id,a.id,b.id FROM l a JOIN r b USING(id) WHERE id=2;",
      [[.text "a",.integer 2,.integer 2]]),
    ("SELECT 1 AS chosen,0 AS chosen FROM l a JOIN r b ON a.id=b.id WHERE chosen;",
      [[.integer 1,.integer 0],[.integer 1,.integer 0]]),
    ("SELECT 0 AS true FROM l a JOIN r b ON a.id=b.id WHERE true;", []),
    ("SELECT 1 AS false FROM l a JOIN r b ON a.id=b.id WHERE false;", [[.integer 1],[.integer 1]]),
    ("SELECT true AS true FROM l a JOIN r b ON a.id=b.id WHERE true;", [[.integer 1],[.integer 1]]),
    ("SELECT 0 AS true FROM l a JOIN r b ON a.id=b.id WHERE 1 IS true;", [])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"joined alias: {sql}: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"joined alias scope, affinity, collation or Boolean shadowing: {sql}"
  for condition in ["chosen", "chosen COLLATE binary", "likely(chosen)", "chosen AND 1", "1 AND chosen"] do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++
        s!"SELECT a.k AS chosen,a.id,b.id FROM l a LEFT JOIN r b ON {condition} ORDER BY a.id,b.id;") with
      | .ok result => pure result
      | .error message => fail message
    let expected ← match ([[Value.text "01",.integer 1,.integer 1],
        [.text "01",.integer 1,.integer 2],[.text "01",.integer 1,.integer 4]]).mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"alias-replaced ON term retained SQLite's discarded outer-join tag: {condition}"
  for sql in [
      "SELECT b.k AS id FROM l a JOIN r b ON a.id=b.id WHERE id=2;",
      "SELECT a.k AS chosen FROM l a JOIN r b ON a.id=b.id WHERE a.chosen;",
      "SELECT a.k AS first,first AS second FROM l a JOIN r b ON a.id=b.id WHERE second;",
      "SELECT a.k COLLATE missing AS true FROM l a JOIN r b ON a.id=b.id WHERE true=1 LIMIT 0;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"joined aliases hid source ambiguity, qualification, non-recursion or required collation: {sql}"

def expectSQLiteFullUsing : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,Key TEXT,lo);CREATE TABLE r(id INTEGER PRIMARY KEY,kEY NUMERIC,ro);INSERT INTO l VALUES(1,'01','left'),(2,'x','left2');INSERT INTO r VALUES(10,1,'right'),(11,2,'right2');"
  let cases : List (String × List (List Value)) := [
    ("SELECT key,l.key,r.key FROM l FULL JOIN r USING(key) ORDER BY l.id,r.id;",
      [[.integer 2,.null,.integer 2],[.text "01",.text "01",.integer 1],[.text "x",.text "x",.null]]),
    ("SELECT * FROM l FULL JOIN r USING(key) ORDER BY l.id,r.id;",
      [[.null,.integer 2,.null,.integer 11,.text "right2"],
       [.integer 1,.text "01",.text "left",.integer 10,.text "right"],
       [.integer 2,.text "x",.text "left2",.null,.null]]),
    ("SELECT l.*,r.* FROM l FULL JOIN r USING(key) ORDER BY l.id,r.id;",
      [[.null,.integer 2,.null,.integer 11,.integer 2,.text "right2"],
       [.integer 1,.text "01",.text "left",.integer 10,.integer 1,.text "right"],
       [.integer 2,.text "x",.text "left2",.null,.null,.null]]),
    ("SELECT key,r.id FROM l FULL JOIN r USING(key) WHERE key=2 ORDER BY key;",
      [[.integer 2,.integer 11]]),
    ("SELECT key,r.id FROM l FULL JOIN r USING(key) WHERE key='2' ORDER BY key;",
      [[.integer 2,.integer 11]]),
    ("SELECT key,r.id FROM l FULL JOIN r USING(key) WHERE +key='2';", []),
    ("SELECT key,r.id FROM l FULL JOIN r USING(key) WHERE key IN (2,NULL);",
      [[.integer 2,.integer 11]]),
    ("SELECT key FROM l FULL JOIN r USING(key) ORDER BY key;",
      [[.integer 2],[.text "01"],[.text "x"]]),
    ("SELECT key AS selected FROM l FULL JOIN r USING(key) ORDER BY selected DESC LIMIT 2;",
      [[.text "x"],[.text "01"]]),
    ("SELECT id,key,l.id,r.id FROM l NATURAL FULL JOIN r ORDER BY id;",
      [[.integer 1,.text "01",.integer 1,.null],[.integer 2,.text "x",.integer 2,.null],
       [.integer 10,.integer 1,.null,.integer 10],[.integer 11,.integer 2,.null,.integer 11]])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"FULL USING: {sql}: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"FULL USING merged values, comparison affinity or ordering: {sql}"
  let (created, _) ← match CoreSQL.execute Core.State.empty (setup ++
      "CREATE TABLE named AS SELECT key,(key),+key,key COLLATE binary,likely(key) FROM l FULL JOIN r USING(key);") with
    | .ok result => pure result
    | .error message => fail message
  let some table := created.database.findTable? "named" | fail "FULL USING CTAS missing"
  unless table.schema.visibleColumns.map (·.name) == ["key","(key)","+key","key COLLATE binary","likely(key)"] &&
      table.schema.visibleColumns.map (·.affinity) == [.text,.text,.blob,.text,.blob] do
    fail "FULL USING CTAS lost original expression spelling or inherited affinity"

def expectSQLiteRightUsing : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,Key TEXT,lo);CREATE TABLE r(id INTEGER PRIMARY KEY,kEY NUMERIC,ro);INSERT INTO l VALUES(1,'01','left'),(2,'x','left2');INSERT INTO r VALUES(10,1,'right'),(11,2,'right2');"
  let cases : List (String × List (List Value)) := [
    ("SELECT key,l.key,r.key FROM l RIGHT JOIN r USING(key) ORDER BY r.id;",
      [[.integer 1,.text "01",.integer 1],[.integer 2,.null,.integer 2]]),
    ("SELECT * FROM l RIGHT JOIN r USING(key) ORDER BY r.id;",
      [[.integer 1,.integer 1,.text "left",.integer 10,.text "right"],
       [.null,.integer 2,.null,.integer 11,.text "right2"]]),
    ("SELECT l.*,r.* FROM l RIGHT JOIN r USING(key) ORDER BY r.id;",
      [[.integer 1,.integer 1,.text "left",.integer 10,.integer 1,.text "right"],
       [.null,.integer 2,.null,.integer 11,.integer 2,.text "right2"]]),
    ("SELECT key,r.id FROM l RIGHT JOIN r USING(key) WHERE key='01' ORDER BY key;",
      [[.integer 1,.integer 10]]),
    ("SELECT key,r.id FROM l RIGHT JOIN r USING(key) WHERE +key='01';", []),
    ("SELECT key,r.id FROM l RIGHT JOIN r USING(key) ORDER BY key DESC LIMIT 1;",
      [[.integer 2,.integer 11]]),
    ("SELECT id,key,l.id FROM l NATURAL RIGHT JOIN r ORDER BY id;",
      [[.integer 10,.integer 1,.null],[.integer 11,.integer 2,.null]])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"RIGHT USING: {sql}: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"RIGHT USING merged values, affinity or qualification: {sql}"
  let (created, _) ← match CoreSQL.execute Core.State.empty (setup ++
      "CREATE TABLE starred AS SELECT * FROM l RIGHT JOIN r USING(key);" ++
      "CREATE TABLE named AS SELECT key,l.key,r.key FROM l RIGHT JOIN r USING(key);") with
    | .ok result => pure result
    | .error message => fail message
  let some starred := created.database.findTable? "starred" | fail "RIGHT USING star CTAS missing"
  let some named := created.database.findTable? "named" | fail "RIGHT USING named CTAS missing"
  unless starred.schema.visibleColumns.map (·.name) == ["id","Key","lo","id:1","ro"] &&
      (starred.schema.visibleColumns[1]?).map (·.affinity) == some .numeric &&
      named.schema.visibleColumns.map (·.name) == ["kEY","Key:1","kEY:2"] &&
      named.schema.visibleColumns.map (·.affinity) == [.numeric,.text,.numeric] do
    fail "RIGHT USING CTAS lost original star spelling or replacement-column affinity"

def expectSQLiteRightFullJoins : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);INSERT INTO l VALUES(1,'A'),(2,'B'),(4,'D');INSERT INTO r VALUES(2,'b'),(3,'C'),(5,'E');"
  let cases : List (String × List (List Value)) := [
    ("SELECT a.id,b.id FROM l a RIGHT JOIN r b ON a.id=b.id ORDER BY a.id,b.id;",
      [[.null,.integer 3],[.null,.integer 5],[.integer 2,.integer 2]]),
    ("SELECT a.id,b.id FROM l a FULL OUTER JOIN r b ON a.id=b.id ORDER BY a.id,b.id;",
      [[.null,.integer 3],[.null,.integer 5],[.integer 1,.null],[.integer 2,.integer 2],[.integer 4,.null]]),
    ("SELECT a.id,b.id FROM l a FULL JOIN r b ON a.id=b.id WHERE b.id IS NULL ORDER BY a.id,b.id;",
      [[.integer 1,.null],[.integer 4,.null]]),
    ("SELECT a.id,b.id FROM l a FULL JOIN r b ON a.id=b.id WHERE a.id IS NULL ORDER BY a.id,b.id;",
      [[.null,.integer 3],[.null,.integer 5]]),
    ("SELECT a.id,b.id FROM l a RIGHT JOIN r b ON a.id=b.id WHERE a.id=1 ORDER BY a.id,b.id;", [])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"RIGHT/FULL join: {sql}: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"RIGHT/FULL null extension or WHERE accounting: {sql}"
  let empty := "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);INSERT INTO r VALUES(2,'b');"
  let (_, output) ← match CoreSQL.execute Core.State.empty (empty ++
      "SELECT a.id,b.id FROM l a FULL JOIN r b ON abs(-9223372036854775808);") with
    | .ok result => pure result
    | .error message => fail message
  let expected ← match [[Value.null,.integer 2]].mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some expected do fail "empty FULL JOIN evaluated ON or lost padding"

end SQLeanite.Tests
