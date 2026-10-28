import SQLeaniteTests.ExpectSQLiteJsonSubtype
import SQLeaniteTests.ExpectSQLitePragmaArguments

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectSQLiteJsonBinaryEscapes : IO Unit := do
  -- All 39 distinct failures from the preserved expanded binary-escape corpus.
  let cases : List (String × List Value) := [
    ("e8000000025c00", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("7be8000000025c00", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'array'", .text "1"]),
    ("9c1761e8000000025c00", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"]),
    ("f800000000000000035c0061", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("cb0cf800000000000000035c0061", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'array'", .text "1"]),
    ("cc0e1761f800000000000000035c0061", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"]),
    ("f80000000000000003615c00", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("cb0cf80000000000000003615c00", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'array'", .text "1"]),
    ("cc0e1761f80000000000000003615c00", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"]),
    ("48615c0061", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("5b48615c0061", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'array'", .text "1"]),
    ("7c176148615c0061", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"]),
    ("f900000000000000025c00", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("bbf900000000000000025c00", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'array'", .text "1"]),
    ("cc0d1761f900000000000000025c00", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"]),
    ("395c0061", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("4b395c0061", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'array'", .text "1"]),
    ("6c1761395c0061", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"]),
    ("39615c00", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("4b39615c00", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'array'", .text "1"]),
    ("6c176139615c00", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"]),
    ("c904615c0061", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("6bc904615c0061", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'array'", .text "1"]),
    ("8c1761c904615c0061", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"]),
    ("695c0af299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("7b695c0af299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .null, .null]),
    ("9c1761695c0af299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"]),
    ("695c0df299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("7b695c0df299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .null, .null]),
    ("9c1761695c0df299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"]),
    ("795c0d0af299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("8b795c0d0af299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'array'", .text "1"]),
    ("ac1761795c0d0af299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"]),
    ("895ce280a8f299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("9b895ce280a8f299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'array'", .text "1"]),
    ("bc1761895ce280a8f299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"]),
    ("895ce280a9f299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'text'", .text "0"]),
    ("9b895ce280a9f299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'array'", .text "1"]),
    ("bc1761895ce280a9f299a699", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .text "'object'", .text "0"])]
  for (hex, expected) in cases do
    let fields := ["json_valid(v)"] ++ (List.range 15).map (fun index => s!"json_valid(v,{index+1})") ++
      ["CASE WHEN json_valid(v,4) THEN quote(json_type(v)) END", "CASE WHEN json_valid(v,4) THEN quote(json_array_length(v)) END"]
    let sql := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,X'" ++ hex ++ "');SELECT " ++ String.intercalate "," fields ++ " FROM t;"
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok x => pure x | .error message => fail message
    let wanted ← match expected.mapM SQLSurface.value with
      | .ok row => pure row | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [wanted] do
      fail s!"binary JSON escape differs from C: {hex}"

def expectSQLiteDateTime : IO Unit := do
  let controls : List (String × String) := [
  ("SELECT typeof(date('2001-02-03')),quote(date('2001-02-03')),hex(CAST(date('2001-02-03') AS BLOB));", "text|'2001-02-03'|323030312D30322D3033"),
  ("SELECT typeof(strftime('%Y-%m-%d %H:%M:%S','2001-02-03')),quote(strftime('%Y-%m-%d %H:%M:%S','2001-02-03')),hex(CAST(strftime('%Y-%m-%d %H:%M:%S','2001-02-03') AS BLOB));", "text|'2001-02-03 00:00:00'|323030312D30322D30332030303A30303A3030"),
  ("SELECT typeof(unixepoch('2024-02-29')),quote(unixepoch('2024-02-29')),hex(CAST(unixepoch('2024-02-29') AS BLOB));", "integer|1709164800|31373039313634383030"),
  ("SELECT typeof(julianday('2023-02-31')),quote(julianday('2023-02-31')),hex(CAST(julianday('2023-02-31') AS BLOB));", "real|2460006.5|323436303030362E35"),
  ("SELECT typeof(datetime('2024-04-31')),quote(datetime('2024-04-31')),hex(CAST(datetime('2024-04-31') AS BLOB));", "text|'2024-05-01 00:00:00'|323032342D30352D30312030303A30303A3030"),
  ("SELECT typeof(time('0000-01-01')),quote(time('0000-01-01')),hex(CAST(time('0000-01-01') AS BLOB));", "text|'00:00:00'|30303A30303A3030"),
  ("SELECT typeof(date('-0001-12-31')),quote(date('-0001-12-31')),hex(CAST(date('-0001-12-31') AS BLOB));", "text|'-0001-12-31'|2D303030312D31322D3331"),
  ("SELECT typeof(strftime('abc%','-0001-12-31')),quote(strftime('abc%','-0001-12-31')),hex(CAST(strftime('abc%','-0001-12-31') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(unixepoch('-4713-11-24 12:00:00')),quote(unixepoch('-4713-11-24 12:00:00')),hex(CAST(unixepoch('-4713-11-24 12:00:00') AS BLOB));", "integer|-210866760000|2D323130383636373630303030"),
  ("SELECT typeof(julianday('9999-12-31 23:59:59.999')),quote(julianday('9999-12-31 23:59:59.999')),hex(CAST(julianday('9999-12-31 23:59:59.999') AS BLOB));", "real|5373484.4999999888|353337333438342E34393939393939383838"),
  ("SELECT typeof(datetime('2024-01-01 24:15:31.1234')),quote(datetime('2024-01-01 24:15:31.1234')),hex(CAST(datetime('2024-01-01 24:15:31.1234') AS BLOB));", "text|'2024-01-01 24:15:31'|323032342D30312D30312032343A31353A3331"),
  ("SELECT typeof(time('2024-01-31 24:15:31')),quote(time('2024-01-31 24:15:31')),hex(CAST(time('2024-01-31 24:15:31') AS BLOB));", "text|'24:15:31'|32343A31353A3331"),
  ("SELECT typeof(date('12:34')),quote(date('12:34')),hex(CAST(date('12:34') AS BLOB));", "text|'2000-01-01'|323030302D30312D3031"),
  ("SELECT typeof(strftime('%d|%e|%H|%k|%I|%l|%p|%P|%%','12:34')),quote(strftime('%d|%e|%H|%k|%I|%l|%p|%P|%%','12:34')),hex(CAST(strftime('%d|%e|%H|%k|%I|%l|%p|%P|%%','12:34') AS BLOB));", "text|'01| 1|12|12|12|12|PM|pm|%'|30317C20317C31327C31327C31327C31327C504D7C706D7C25"),
  ("SELECT typeof(unixepoch('12:34:56.999999')),quote(unixepoch('12:34:56.999999')),hex(CAST(unixepoch('12:34:56.999999') AS BLOB));", "integer|946730096|393436373330303936"),
  ("SELECT typeof(julianday('2001-02-03TT 04:05:06+14:59')),quote(julianday('2001-02-03TT 04:05:06+14:59')),hex(CAST(julianday('2001-02-03TT 04:05:06+14:59') AS BLOB));", "real|2451943.0459027779|323435313934332E30343539303237373739"),
  ("SELECT typeof(datetime('2001-02-03 04:05:06 -00:30')),quote(datetime('2001-02-03 04:05:06 -00:30')),hex(CAST(datetime('2001-02-03 04:05:06 -00:30') AS BLOB));", "text|'2001-02-03 04:35:06'|323030312D30322D30332030343A33353A3036"),
  ("SELECT typeof(time('2001-02-03 04:05:06.0005Z')),quote(time('2001-02-03 04:05:06.0005Z')),hex(CAST(time('2001-02-03 04:05:06.0005Z') AS BLOB));", "text|'04:05:06'|30343A30353A3036"),
  ("SELECT typeof(date(0)),quote(date(0)),hex(CAST(date(0) AS BLOB));", "text|'-4713-11-24'|2D343731332D31312D3234"),
  ("SELECT typeof(strftime('%F|%T|%f|%s|%J',0)),quote(strftime('%F|%T|%f|%s|%J',0)),hex(CAST(strftime('%F|%T|%f|%s|%J',0) AS BLOB));", "text|'-4713-11-24|12:00:00|00.000|-210866760000|0'|2D343731332D31312D32347C31323A30303A30307C30302E3030307C2D3231303836363736303030307C30"),
  ("SELECT typeof(unixepoch(2451544.5)),quote(unixepoch(2451544.5)),hex(CAST(unixepoch(2451544.5) AS BLOB));", "integer|946684800|393436363834383030"),
  ("SELECT typeof(julianday(5373484.49999)),quote(julianday(5373484.49999)),hex(CAST(julianday(5373484.49999) AS BLOB));", "real|5373484.49999|353337333438342E3439393939"),
  ("SELECT typeof(datetime(5373484.5)),quote(datetime(5373484.5)),hex(CAST(datetime(5373484.5) AS BLOB));", "null|NULL|"),
  ("SELECT typeof(time(-1)),quote(time(-1)),hex(CAST(time(-1) AS BLOB));", "null|NULL|"),
  ("SELECT typeof(date(NULL)),quote(date(NULL)),hex(CAST(date(NULL) AS BLOB));", "null|NULL|"),
  ("SELECT typeof(strftime('',NULL)),quote(strftime('',NULL)),hex(CAST(strftime('',NULL) AS BLOB));", "null|NULL|"),
  ("SELECT typeof(unixepoch('not a date')),quote(unixepoch('not a date')),hex(CAST(unixepoch('not a date') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(julianday('2024-00-01')),quote(julianday('2024-00-01')),hex(CAST(julianday('2024-00-01') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(datetime('2024-01-32')),quote(datetime('2024-01-32')),hex(CAST(datetime('2024-01-32') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(time('2001-02-03 25:00')),quote(time('2001-02-03 25:00')),hex(CAST(time('2001-02-03 25:00') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(date('2001-02-03 12:34:60')),quote(date('2001-02-03 12:34:60')),hex(CAST(date('2001-02-03 12:34:60') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(strftime('%Q','2001-02-03 12:34:60')),quote(strftime('%Q','2001-02-03 12:34:60')),hex(CAST(strftime('%Q','2001-02-03 12:34:60') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(unixepoch(' 2001-02-03')),quote(unixepoch(' 2001-02-03')),hex(CAST(unixepoch(' 2001-02-03') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(julianday('2001-02-03\t')),quote(julianday('2001-02-03\t')),hex(CAST(julianday('2001-02-03\t') AS BLOB));", "real|2451943.5|323435313934332E35"),
  ("SELECT typeof(datetime(CAST(x'323030312D30322D303300ff' AS TEXT))),quote(datetime(CAST(x'323030312D30322D303300ff' AS TEXT))),hex(CAST(datetime(CAST(x'323030312D30322D303300ff' AS TEXT)) AS BLOB));", "text|'2001-02-03 00:00:00'|323030312D30322D30332030303A30303A3030"),
  ("SELECT typeof(time(x'323030312D30322D3033')),quote(time(x'323030312D30322D3033')),hex(CAST(time(x'323030312D30322D3033') AS BLOB));", "text|'00:00:00'|30303A30303A3030"),
  ("SELECT typeof(date(x'ff323030312D30322D3033')),quote(date(x'ff323030312D30322D3033')),hex(CAST(date(x'ff323030312D30322D3033') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(strftime('%G|%g|%V|%j|%U|%W|%u|%w',x'ff323030312D30322D3033')),quote(strftime('%G|%g|%V|%j|%U|%W|%u|%w',x'ff323030312D30322D3033')),hex(CAST(strftime('%G|%g|%V|%j|%U|%W|%u|%w',x'ff323030312D30322D3033') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(unixepoch('2451544.5junk')),quote(unixepoch('2451544.5junk')),hex(CAST(unixepoch('2451544.5junk') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(time('2024-01-31 12:34:56.789','+1 day')),quote(time('2024-01-31 12:34:56.789','+1 day')),hex(CAST(time('2024-01-31 12:34:56.789','+1 day') AS BLOB));", "text|'12:34:56'|31323A33343A3536"),
  ("SELECT typeof(unixepoch('2023-02-31','-1.25 days')),quote(unixepoch('2023-02-31','-1.25 days')),hex(CAST(unixepoch('2023-02-31','-1.25 days') AS BLOB));", "integer|1677693600|31363737363933363030"),
  ("SELECT typeof(strftime('%Q',1700000000,'+1 month','floor')),quote(strftime('%Q',1700000000,'+1 month','floor')),hex(CAST(strftime('%Q',1700000000,'+1 month','floor') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(date('2024-01-31 12:34:56.789','start of month','+1 month','-1 day')),quote(date('2024-01-31 12:34:56.789','start of month','+1 month','-1 day')),hex(CAST(date('2024-01-31 12:34:56.789','start of month','+1 month','-1 day') AS BLOB));", "text|'2024-01-31'|323032342D30312D3331"),
  ("SELECT typeof(julianday('2023-02-31','start of year')),quote(julianday('2023-02-31','start of year')),hex(CAST(julianday('2023-02-31','start of year') AS BLOB));", "real|2459945.5|323435393934352E35"),
  ("SELECT typeof(unixepoch(1700000000,'weekday 0')),quote(unixepoch(1700000000,'weekday 0')),hex(CAST(unixepoch(1700000000,'weekday 0') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(strftime('%Q','2024-01-31 12:34:56.789','subsec')),quote(strftime('%Q','2024-01-31 12:34:56.789','subsec')),hex(CAST(strftime('%Q','2024-01-31 12:34:56.789','subsec') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(datetime('2023-02-31','floor')),quote(datetime('2023-02-31','floor')),hex(CAST(datetime('2023-02-31','floor') AS BLOB));", "text|'2023-02-28 00:00:00'|323032332D30322D32382030303A30303A3030"),
  ("SELECT typeof(julianday(1700000000,'ceiling')),quote(julianday(1700000000,'ceiling')),hex(CAST(julianday(1700000000,'ceiling') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(unixepoch('2024-01-31 12:34:56.789','auto')),quote(unixepoch('2024-01-31 12:34:56.789','auto')),hex(CAST(unixepoch('2024-01-31 12:34:56.789','auto') AS BLOB));", "integer|1706704496|31373036373034343936"),
  ("SELECT typeof(time('2023-02-31','unixepoch')),quote(time('2023-02-31','unixepoch')),hex(CAST(time('2023-02-31','unixepoch') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(datetime(1700000000,'-00:01:02.123')),quote(datetime(1700000000,'-00:01:02.123')),hex(CAST(datetime(1700000000,'-00:01:02.123') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(julianday('2024-01-31 12:34:56.789','-0000-01-00')),quote(julianday('2024-01-31 12:34:56.789','-0000-01-00')),hex(CAST(julianday('2024-01-31 12:34:56.789','-0000-01-00') AS BLOB));", "real|2460310.0242683911|323436303331302E30323432363833393131"),
  ("SELECT typeof(date('2023-02-31','+0.25 year')),quote(date('2023-02-31','+0.25 year')),hex(CAST(date('2023-02-31','+0.25 year') AS BLOB));", "text|'2023-06-02'|323032332D30362D3032"),
  ("SELECT typeof(time(1700000000,'weekday 7')),quote(time(1700000000,'weekday 7')),hex(CAST(time(1700000000,'weekday 7') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(datetime('2024-01-31 12:34:56.789','+1 day ')),quote(datetime('2024-01-31 12:34:56.789','+1 day ')),hex(CAST(datetime('2024-01-31 12:34:56.789','+1 day ') AS BLOB));", "null|NULL|"),
  ("SELECT typeof(strftime('','2023-02-31','+1 day','unixepoch')),quote(strftime('','2023-02-31','+1 day','unixepoch')),hex(CAST(strftime('','2023-02-31','+1 day','unixepoch') AS BLOB));", "null|NULL|")]
  for (sql, expected) in controls do
    match CoreSQL.execute Core.State.empty sql with
    | .error message => fail s!"date/time rejected {sql}: {message}"
    | .ok (_, results) =>
        let rows ← match (results.flatMap (fun result => result.rows)).mapM (fun row => row.mapM CoreExpr.value) with
          | .ok values => pure values | .error message => fail message
        let actual := String.intercalate "\n" (rows.map fun row => String.intercalate "|" (row.map toString))
        unless actual == expected do fail s!"date/time output {sql}: {actual}; expected {expected}"

def expectSQLiteTimeDifference : IO Unit := do
  let controls : List (String × Bool × String) := [
  ("SELECT typeof(timediff('2023-02-15','2023-02-15')),quote(timediff('2023-02-15','2023-02-15')),datetime('2023-02-15',timediff('2023-02-15','2023-02-15')),datetime('2023-02-15');", false, "text|'+0000-00-00 00:00:00.000'|2023-02-15 00:00:00|2023-02-15 00:00:00"),
  ("SELECT typeof(timediff('2023-02-15','2001-02-03 04:05:06.789+01:30')),quote(timediff('2023-02-15','2001-02-03 04:05:06.789+01:30')),datetime('2001-02-03 04:05:06.789+01:30',timediff('2023-02-15','2001-02-03 04:05:06.789+01:30')),datetime('2023-02-15');", false, "text|'+0022-00-11 21:24:53.211'|2023-02-15 00:00:00|2023-02-15 00:00:00"),
  ("SELECT typeof(timediff('2023-03-15','2023-02-31')),quote(timediff('2023-03-15','2023-02-31')),datetime('2023-02-31',timediff('2023-03-15','2023-02-31')),datetime('2023-03-15');", false, "text|'+0000-00-12 00:00:00.000'|2023-03-15 00:00:00|2023-03-15 00:00:00"),
  ("SELECT typeof(timediff('2023-03-15','invalid')),quote(timediff('2023-03-15','invalid')),datetime('invalid',timediff('2023-03-15','invalid')),datetime('2023-03-15');", false, "null|NULL||2023-03-15 00:00:00"),
  ("SELECT typeof(timediff('2023-04-15','2000-01-01 24:05')),quote(timediff('2023-04-15','2000-01-01 24:05')),datetime('2000-01-01 24:05',timediff('2023-04-15','2000-01-01 24:05')),datetime('2023-04-15');", false, "text|'+0023-03-12 23:55:00.000'|2023-04-15 00:00:00|2023-04-15 00:00:00"),
  ("SELECT typeof(timediff('2024-01-31','2024-02-29')),quote(timediff('2024-01-31','2024-02-29')),datetime('2024-02-29',timediff('2024-01-31','2024-02-29')),datetime('2024-01-31');", false, "text|'-0000-00-29 00:00:00.000'|2024-01-31 00:00:00|2024-01-31 00:00:00"),
  ("SELECT typeof(timediff('2024-01-31',NULL)),quote(timediff('2024-01-31',NULL)),datetime(NULL,timediff('2024-01-31',NULL)),datetime('2024-01-31');", false, "null|NULL||2024-01-31 00:00:00"),
  ("SELECT typeof(timediff('2024-02-29','9999-12-31 23:59:59.999')),quote(timediff('2024-02-29','9999-12-31 23:59:59.999')),datetime('9999-12-31 23:59:59.999',timediff('2024-02-29','9999-12-31 23:59:59.999')),datetime('2024-02-29');", false, "text|'-7975-10-02 23:59:59.999'|2024-02-29 00:00:00|2024-02-29 00:00:00"),
  ("SELECT typeof(timediff('2023-02-31','2024-01-31')),quote(timediff('2023-02-31','2024-01-31')),datetime('2024-01-31',timediff('2023-02-31','2024-01-31')),datetime('2023-02-31');", false, "text|'-0000-10-28 00:00:00.000'|2023-03-03 00:00:00|2023-03-03 00:00:00"),
  ("SELECT typeof(timediff('2023-02-31',5373484.49999)),quote(timediff('2023-02-31',5373484.49999)),datetime(5373484.49999,timediff('2023-02-31',5373484.49999)),datetime('2023-02-31');", false, "text|'-7976-09-28 23:59:59.136'|2023-03-03 00:00:00|2023-03-03 00:00:00"),
  ("SELECT typeof(timediff('0000-01-01','-4713-11-24 12:00:00')),quote(timediff('0000-01-01','-4713-11-24 12:00:00')),datetime('-4713-11-24 12:00:00',timediff('0000-01-01','-4713-11-24 12:00:00')),datetime('0000-01-01');", false, "text|'+4712-01-07 12:00:00.000'|0000-01-01 00:00:00|0000-01-01 00:00:00"),
  ("SELECT typeof(timediff('-0001-12-31','2023-04-15')),quote(timediff('-0001-12-31','2023-04-15')),datetime('2023-04-15',timediff('-0001-12-31','2023-04-15')),datetime('-0001-12-31');", false, "text|'-2023-03-15 00:00:00.000'|-0001-12-31 00:00:00|-0001-12-31 00:00:00"),
  ("SELECT typeof(timediff('-0001-12-31',0)),quote(timediff('-0001-12-31',0)),datetime(0,timediff('-0001-12-31',0)),datetime('-0001-12-31');", false, "text|'+4712-01-06 12:00:00.000'|-0001-12-31 00:00:00|-0001-12-31 00:00:00"),
  ("SELECT typeof(timediff('-4713-11-24 12:00:00','-0001-12-31')),quote(timediff('-4713-11-24 12:00:00','-0001-12-31')),datetime('-0001-12-31',timediff('-4713-11-24 12:00:00','-0001-12-31')),datetime('-4713-11-24 12:00:00');", false, "text|'-4712-01-06 12:00:00.000'|-4713-11-24 12:00:00|-4713-11-24 12:00:00"),
  ("SELECT typeof(timediff('9999-12-31 23:59:59.999','2023-03-15')),quote(timediff('9999-12-31 23:59:59.999','2023-03-15')),datetime('2023-03-15',timediff('9999-12-31 23:59:59.999','2023-03-15')),datetime('9999-12-31 23:59:59.999');", false, "text|'+7976-09-16 23:59:59.999'|9999-12-31 23:59:59|9999-12-31 23:59:59"),
  ("SELECT typeof(timediff('9999-12-31 23:59:59.999',2451544.5)),quote(timediff('9999-12-31 23:59:59.999',2451544.5)),datetime(2451544.5,timediff('9999-12-31 23:59:59.999',2451544.5)),datetime('9999-12-31 23:59:59.999');", false, "text|'+7999-11-30 23:59:59.999'|9999-12-31 23:59:59|9999-12-31 23:59:59"),
  ("SELECT typeof(timediff('2000-01-01 24:05','0000-01-01')),quote(timediff('2000-01-01 24:05','0000-01-01')),datetime('0000-01-01',timediff('2000-01-01 24:05','0000-01-01')),datetime('2000-01-01 24:05');", false, "text|'+2000-00-01 00:05:00.000'|2000-01-02 00:05:00|2000-01-01 24:05:00"),
  ("SELECT typeof(timediff('2001-02-03 04:05:06.789+01:30','2023-02-15')),quote(timediff('2001-02-03 04:05:06.789+01:30','2023-02-15')),datetime('2023-02-15',timediff('2001-02-03 04:05:06.789+01:30','2023-02-15')),datetime('2001-02-03 04:05:06.789+01:30');", false, "text|'-0022-00-11 21:24:53.211'|2001-02-03 02:35:06|2001-02-03 02:35:06"),
  ("SELECT typeof(timediff('2001-02-03 04:05:06.789+01:30','2001-02-03 04:05:06.789+01:30')),quote(timediff('2001-02-03 04:05:06.789+01:30','2001-02-03 04:05:06.789+01:30')),datetime('2001-02-03 04:05:06.789+01:30',timediff('2001-02-03 04:05:06.789+01:30','2001-02-03 04:05:06.789+01:30')),datetime('2001-02-03 04:05:06.789+01:30');", false, "text|'+0000-00-00 00:00:00.000'|2001-02-03 02:35:06|2001-02-03 02:35:06"),
  ("SELECT typeof(timediff(2451544.5,'2023-02-31')),quote(timediff(2451544.5,'2023-02-31')),datetime('2023-02-31',timediff(2451544.5,'2023-02-31')),datetime(2451544.5);", false, "text|'-0023-02-02 00:00:00.000'|1999-12-29 00:00:00|2000-01-01 00:00:00"),
  ("SELECT typeof(timediff(2451544.5,'invalid')),quote(timediff(2451544.5,'invalid')),datetime('invalid',timediff(2451544.5,'invalid')),datetime(2451544.5);", false, "null|NULL||2000-01-01 00:00:00"),
  ("SELECT typeof(timediff(0,'2000-01-01 24:05')),quote(timediff(0,'2000-01-01 24:05')),datetime('2000-01-01 24:05',timediff(0,'2000-01-01 24:05')),datetime(0);", false, "text|'-6712-01-07 12:05:00.000'|-4713-11-24 12:00:00|-4713-11-24 12:00:00"),
  ("SELECT typeof(timediff(5373484.49999,'2024-02-29')),quote(timediff(5373484.49999,'2024-02-29')),datetime('2024-02-29',timediff(5373484.49999,'2024-02-29')),datetime(5373484.49999);", false, "text|'+7975-10-02 23:59:59.136'|9999-12-31 23:59:59|9999-12-31 23:59:59"),
  ("SELECT typeof(timediff(5373484.49999,NULL)),quote(timediff(5373484.49999,NULL)),datetime(NULL,timediff(5373484.49999,NULL)),datetime(5373484.49999);", false, "null|NULL||9999-12-31 23:59:59"),
  ("SELECT typeof(timediff(NULL,'9999-12-31 23:59:59.999')),quote(timediff(NULL,'9999-12-31 23:59:59.999')),datetime('9999-12-31 23:59:59.999',timediff(NULL,'9999-12-31 23:59:59.999')),datetime(NULL);", false, "null|NULL||"),
  ("SELECT typeof(timediff('invalid','2024-01-31')),quote(timediff('invalid','2024-01-31')),datetime('2024-01-31',timediff('invalid','2024-01-31')),datetime('invalid');", false, "null|NULL||"),
  ("SELECT typeof(timediff('invalid',5373484.49999)),quote(timediff('invalid',5373484.49999)),datetime(5373484.49999,timediff('invalid',5373484.49999)),datetime('invalid');", false, "null|NULL||"),
  ("SELECT timediff();", true, "wrong number of arguments to function timediff()"),
  ("SELECT timediff(NULL);", true, "wrong number of arguments to function timediff()"),
  ("SELECT timediff(DISTINCT 1);", true, "wrong number of arguments to function timediff()"),
  ("SELECT timediff(missing);", true, "no such column: missing"),
  ("SELECT TIMEDIFF();", true, "wrong number of arguments to function TIMEDIFF()"),
  ("SELECT TIMEDIFF(NULL);", true, "wrong number of arguments to function TIMEDIFF()"),
  ("SELECT TIMEDIFF(DISTINCT 1);", true, "wrong number of arguments to function TIMEDIFF()"),
  ("SELECT TIMEDIFF(missing);", true, "no such column: missing"),
  ("SELECT \"timediff\"();", true, "wrong number of arguments to function timediff()"),
  ("SELECT \"timediff\"(NULL);", true, "wrong number of arguments to function timediff()"),
  ("SELECT \"timediff\"(DISTINCT 1);", true, "wrong number of arguments to function timediff()"),
  ("SELECT \"timediff\"(missing);", true, "no such column: missing"),
  ("SELECT [timediff]();", true, "wrong number of arguments to function timediff()"),
  ("SELECT [timediff](NULL);", true, "wrong number of arguments to function timediff()"),
  ("SELECT [timediff](DISTINCT 1);", true, "wrong number of arguments to function timediff()"),
  ("SELECT [timediff](missing);", true, "no such column: missing")]
  for (sql, failed, expected) in controls do
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless failed && message == expected do
        fail s!"timediff rejected {sql}: {message}; expected {expected}"
    | .ok (_, results) =>
        let rows ← match (results.flatMap (fun result => result.rows)).mapM (fun row => row.mapM CoreExpr.value) with
          | .ok values => pure values | .error message => fail message
        let actual := String.intercalate "\n" (rows.map fun row => String.intercalate "|" (row.map toString))
        unless !failed && actual == expected do fail s!"timediff output {sql}: {actual}; expected {expected}"

def expectSQLiteDateNull : IO Unit := do
  let controls : List (String × Bool × String) := [
  ("SELECT typeof(date('now',NULL)),quote(date('now',NULL)),hex(CAST(date('now',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(date('now','localtime',NULL)),quote(date('now','localtime',NULL)),hex(CAST(date('now','localtime',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(date(NULL,'utc')),quote(date(NULL,'utc')),hex(CAST(date(NULL,'utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(date('invalid','utc')),quote(date('invalid','utc')),hex(CAST(date('invalid','utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(date('2001-02-03','unknown modifier','utc')),quote(date('2001-02-03','unknown modifier','utc')),hex(CAST(date('2001-02-03','unknown modifier','utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(date('subsec',NULL)),quote(date('subsec',NULL)),hex(CAST(date('subsec',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(date(NULL,abs(-9223372036854775808))),quote(date(NULL,abs(-9223372036854775808))),hex(CAST(date(NULL,abs(-9223372036854775808)) AS BLOB));", true, "integer overflow"),
  ("SELECT typeof(date(NULL,json('malformed'))),quote(date(NULL,json('malformed'))),hex(CAST(date(NULL,json('malformed')) AS BLOB));", true, "malformed JSON"),
  ("SELECT typeof(time('now',NULL)),quote(time('now',NULL)),hex(CAST(time('now',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(time('now','localtime',NULL)),quote(time('now','localtime',NULL)),hex(CAST(time('now','localtime',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(time(NULL,'utc')),quote(time(NULL,'utc')),hex(CAST(time(NULL,'utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(time('invalid','utc')),quote(time('invalid','utc')),hex(CAST(time('invalid','utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(time('2001-02-03','unknown modifier','utc')),quote(time('2001-02-03','unknown modifier','utc')),hex(CAST(time('2001-02-03','unknown modifier','utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(time('subsec',NULL)),quote(time('subsec',NULL)),hex(CAST(time('subsec',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(time(NULL,abs(-9223372036854775808))),quote(time(NULL,abs(-9223372036854775808))),hex(CAST(time(NULL,abs(-9223372036854775808)) AS BLOB));", true, "integer overflow"),
  ("SELECT typeof(time(NULL,json('malformed'))),quote(time(NULL,json('malformed'))),hex(CAST(time(NULL,json('malformed')) AS BLOB));", true, "malformed JSON"),
  ("SELECT typeof(datetime('now',NULL)),quote(datetime('now',NULL)),hex(CAST(datetime('now',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(datetime('now','localtime',NULL)),quote(datetime('now','localtime',NULL)),hex(CAST(datetime('now','localtime',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(datetime(NULL,'utc')),quote(datetime(NULL,'utc')),hex(CAST(datetime(NULL,'utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(datetime('invalid','utc')),quote(datetime('invalid','utc')),hex(CAST(datetime('invalid','utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(datetime('2001-02-03','unknown modifier','utc')),quote(datetime('2001-02-03','unknown modifier','utc')),hex(CAST(datetime('2001-02-03','unknown modifier','utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(datetime('subsec',NULL)),quote(datetime('subsec',NULL)),hex(CAST(datetime('subsec',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(datetime(NULL,abs(-9223372036854775808))),quote(datetime(NULL,abs(-9223372036854775808))),hex(CAST(datetime(NULL,abs(-9223372036854775808)) AS BLOB));", true, "integer overflow"),
  ("SELECT typeof(datetime(NULL,json('malformed'))),quote(datetime(NULL,json('malformed'))),hex(CAST(datetime(NULL,json('malformed')) AS BLOB));", true, "malformed JSON"),
  ("SELECT typeof(julianday('now',NULL)),quote(julianday('now',NULL)),hex(CAST(julianday('now',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(julianday('now','localtime',NULL)),quote(julianday('now','localtime',NULL)),hex(CAST(julianday('now','localtime',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(julianday(NULL,'utc')),quote(julianday(NULL,'utc')),hex(CAST(julianday(NULL,'utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(julianday('invalid','utc')),quote(julianday('invalid','utc')),hex(CAST(julianday('invalid','utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(julianday('2001-02-03','unknown modifier','utc')),quote(julianday('2001-02-03','unknown modifier','utc')),hex(CAST(julianday('2001-02-03','unknown modifier','utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(julianday('subsec',NULL)),quote(julianday('subsec',NULL)),hex(CAST(julianday('subsec',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(julianday(NULL,abs(-9223372036854775808))),quote(julianday(NULL,abs(-9223372036854775808))),hex(CAST(julianday(NULL,abs(-9223372036854775808)) AS BLOB));", true, "integer overflow"),
  ("SELECT typeof(julianday(NULL,json('malformed'))),quote(julianday(NULL,json('malformed'))),hex(CAST(julianday(NULL,json('malformed')) AS BLOB));", true, "malformed JSON"),
  ("SELECT typeof(unixepoch('now',NULL)),quote(unixepoch('now',NULL)),hex(CAST(unixepoch('now',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(unixepoch('now','localtime',NULL)),quote(unixepoch('now','localtime',NULL)),hex(CAST(unixepoch('now','localtime',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(unixepoch(NULL,'utc')),quote(unixepoch(NULL,'utc')),hex(CAST(unixepoch(NULL,'utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(unixepoch('invalid','utc')),quote(unixepoch('invalid','utc')),hex(CAST(unixepoch('invalid','utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(unixepoch('2001-02-03','unknown modifier','utc')),quote(unixepoch('2001-02-03','unknown modifier','utc')),hex(CAST(unixepoch('2001-02-03','unknown modifier','utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(unixepoch('subsec',NULL)),quote(unixepoch('subsec',NULL)),hex(CAST(unixepoch('subsec',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(unixepoch(NULL,abs(-9223372036854775808))),quote(unixepoch(NULL,abs(-9223372036854775808))),hex(CAST(unixepoch(NULL,abs(-9223372036854775808)) AS BLOB));", true, "integer overflow"),
  ("SELECT typeof(unixepoch(NULL,json('malformed'))),quote(unixepoch(NULL,json('malformed'))),hex(CAST(unixepoch(NULL,json('malformed')) AS BLOB));", true, "malformed JSON"),
  ("SELECT typeof(strftime('%F','now',NULL)),quote(strftime('%F','now',NULL)),hex(CAST(strftime('%F','now',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(strftime('%F','now','localtime',NULL)),quote(strftime('%F','now','localtime',NULL)),hex(CAST(strftime('%F','now','localtime',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(strftime('%F',NULL,'utc')),quote(strftime('%F',NULL,'utc')),hex(CAST(strftime('%F',NULL,'utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(strftime('%F','invalid','utc')),quote(strftime('%F','invalid','utc')),hex(CAST(strftime('%F','invalid','utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(strftime('%F','2001-02-03','unknown modifier','utc')),quote(strftime('%F','2001-02-03','unknown modifier','utc')),hex(CAST(strftime('%F','2001-02-03','unknown modifier','utc') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(strftime('%F','subsec',NULL)),quote(strftime('%F','subsec',NULL)),hex(CAST(strftime('%F','subsec',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(strftime(NULL,'now')),quote(strftime(NULL,'now')),hex(CAST(strftime(NULL,'now') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(strftime(NULL)),quote(strftime(NULL)),hex(CAST(strftime(NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(strftime('%F',NULL,abs(-9223372036854775808))),quote(strftime('%F',NULL,abs(-9223372036854775808))),hex(CAST(strftime('%F',NULL,abs(-9223372036854775808)) AS BLOB));", true, "integer overflow"),
  ("SELECT typeof(strftime('%F',NULL,json('malformed'))),quote(strftime('%F',NULL,json('malformed'))),hex(CAST(strftime('%F',NULL,json('malformed')) AS BLOB));", true, "malformed JSON"),
  ("SELECT typeof(timediff(NULL,'now')),quote(timediff(NULL,'now')),hex(CAST(timediff(NULL,'now') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(timediff('now',NULL)),quote(timediff('now',NULL)),hex(CAST(timediff('now',NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(timediff(NULL,'2001-02-03')),quote(timediff(NULL,'2001-02-03')),hex(CAST(timediff(NULL,'2001-02-03') AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(timediff(NULL,NULL)),quote(timediff(NULL,NULL)),hex(CAST(timediff(NULL,NULL) AS BLOB));", false, "null|NULL|"),
  ("SELECT typeof(timediff(NULL,abs(-9223372036854775808))),quote(timediff(NULL,abs(-9223372036854775808))),hex(CAST(timediff(NULL,abs(-9223372036854775808)) AS BLOB));", true, "integer overflow"),
  ("SELECT typeof(timediff(NULL,json('malformed'))),quote(timediff(NULL,json('malformed'))),hex(CAST(timediff(NULL,json('malformed')) AS BLOB));", true, "malformed JSON")]
  for (sql, failed, expected) in controls do
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless failed && message == expected do
        fail s!"date NULL rejected {sql}: {message}; expected {expected}"
    | .ok (_, results) =>
        let rows ← match (results.flatMap (fun result => result.rows)).mapM (fun row => row.mapM CoreExpr.value) with
          | .ok values => pure values | .error message => fail message
        let actual := String.intercalate "\n" (rows.map fun row => String.intercalate "|" (row.map toString))
        unless !failed && actual == expected do fail s!"date NULL output {sql}: {actual}; expected {expected}"

def expectColdReadChunkPlanning : IO Unit := do
  let accepted := [
    "SELECT id FROM t WHERE id=1; SELECT id FROM t WHERE id=2;",
    "-- prefix\nSELECT v AS \"semi;alias\" FROM t WHERE id=1; /* ; */ SELECT * FROM t WHERE id>=2 LIMIT 3;",
    "SELECT a.id FROM t a JOIN u b ON a.id=b.id;",
    "SELECT id FROM \"semi;table\" WHERE id=4; -- tail;\n",
    "/* comments; only */" ]
  for sql in accepted do
    let whole ← match CoreTokenGrammar.parseStatements sql with
      | .ok result => pure result | .error message => fail message
    let some chunked := CoreLazyFileEngine.parseReadChunks (SQLite.Script.split sql) [] |
      fail s!"cold candidate unexpectedly rejected: {sql}"
    unless reprStr whole.toList == reprStr chunked do
      fail s!"cold chunk certification changed syntax: {sql}"
  for sql in ["SELECT 1; SELECT id FROM t WHERE id=2;",
      "SELECT id FROM t WHERE id=1; INSERT INTO t VALUES(2);",
      "SELECT id FROM t WHERE id=1; SELECT 2;",
      "SELECT id FROM t WHERE id=;", "BEGIN; SELECT id FROM t WHERE id=1;"] do
    unless (CoreLazyFileEngine.parseReadChunks (SQLite.Script.split sql) []).isNone do
      fail s!"cold mixed/invalid batch was accepted: {sql}"

def expectSQLitePragmaListing : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO t VALUES(1,'kept');" with
    | .ok result => pure result
    | .error message => fail message
  -- Captured from the pinned C oracle independently of PragmaSyntax.knownNames.
  let names : List String := ["analysis_limit", "application_id", "auto_vacuum", "automatic_index", "busy_timeout", "cache_size", "cache_spill", "case_sensitive_like", "cell_size_check", "checkpoint_fullfsync", "collation_list", "compile_options", "count_changes", "data_version", "database_list", "default_cache_size", "defer_foreign_keys", "empty_result_callbacks", "encoding", "foreign_key_check", "foreign_key_list", "foreign_keys", "freelist_count", "full_column_names", "fullfsync", "function_list", "hard_heap_limit", "ignore_check_constraints", "incremental_vacuum", "index_info", "index_list", "index_xinfo", "integrity_check", "journal_mode", "journal_size_limit", "legacy_alter_table", "locking_mode", "max_page_count", "mmap_size", "module_list", "optimize", "page_count", "page_size", "pragma_list", "query_only", "quick_check", "read_uncommitted", "recursive_triggers", "reverse_unordered_selects", "schema_version", "secure_delete", "short_column_names", "shrink_memory", "soft_heap_limit", "synchronous", "table_info", "table_list", "table_xinfo", "temp_store", "temp_store_directory", "threads", "trusted_schema", "user_version", "wal_autocheckpoint", "wal_checkpoint", "writable_schema"]
  let expected ← match (names.map fun name => [Value.text name]).mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  for sql in ["PRAGMA pragma_list;", "PRAGMA main.pragma_list=OFF;",
      "PRAGMA temp.PrAgMa_LiSt('ignored;argument');", "PRAGMA pragma_list(+01);"] do
    let (next, results) ← match CoreSQL.execute state sql with
      | .ok result => pure result
      | .error message => fail s!"PRAGMA list {sql}: {message}"
    unless results.map (·.rows) == [expected] && next.database.Equiv state.database &&
        next.headers == state.headers do
      fail s!"PRAGMA list changed names/order/state: {sql}"
  for name in ["pragma_list", "table_info", "table_xinfo", "index_info",
      "index_xinfo", "index_list", "unknown_custom", "application_id", "user_version"] do
    for schema in ["missing", "", "MiXeDé中", "main.part"] do
      let sql := "PRAGMA " ++ CoreFile.quoteIdentifier schema ++ "." ++ name ++ "(t);"
      match CoreSQL.execute state sql with
      | .error message =>
          unless message == s!"unknown database {schema}" do fail s!"PRAGMA schema lost spelling: {sql}: {message}"
      | .ok _ => fail s!"PRAGMA unknown schema accepted: {sql}"

def expectSQLitePragmaSchemaSource : IO Unit := do
  for token in ["missing", "\"MiXeDé中\"", "'single''quote'", "`tick``quote`", "[bracket;name]", "\"\""] do
    for name in ["pragma_list", "table_info", "unknown_custom", "user_version"] do
      let sql := "-- prefix;\nPRAGMA /* before */ " ++ token ++ " /* middle */ . " ++ name ++ "(t);"
      match CoreSourceSQL.execute Core.State.empty sql with
      | .error message =>
          unless message == "unknown database " ++ token do
            fail s!"source schema token not preserved: {sql}: {message}"
      | .ok _ => fail s!"source schema accepted: {sql}"

def expectSQLitePragmaSchemaWriteGuard : IO Unit := do
  for name in ["user_version", "application_id"] do
    let argument : Option Expr := some (.literal (.integer 8))
    for schema in [none, some "main", some "MAIN"] do
      unless CoreFileEngine.requiresWriteAccess Core.State.empty (.pragma name argument schema) do
        fail "a persistent header write lost its access check"
    for schema in ["missing", "", "main.part", "temp", "TEMP"] do
      if CoreFileEngine.requiresWriteAccess Core.State.empty (.pragma name argument (some schema)) then
        fail s!"a non-persistent schema requested file write access: {schema}"

def expectConnectionCounters : IO Unit := do
  let mut state := Core.State.empty
  for source in SQLite.Script.split "CREATE TABLE t(id INTEGER PRIMARY KEY,v INTEGER); BEGIN; INSERT INTO t VALUES(1,10),(2,20); UPDATE t SET v=v; ROLLBACK; SELECT changes(),total_changes();" do
    let parsed ← match CoreTokenGrammar.parseCertified source with
      | .ok parsed => pure parsed
      | .error message => fail message
    for statement in parsed.statements do
      match CoreConnectionSQL.executeStatement state statement source with
      | .error message => fail message
      | .ok (next, _) => state := next
  unless state.lastChanges == 2 && state.totalChanges == 4 do
    fail "connection counters must survive rollback"
  let some table := state.database.findTable? "t" | fail "counter fixture lost table"
  unless table.rows.isEmpty do fail "rollback retained inserted rows"

def expectDerivedQueries : IO Unit := do
  for (sql, expected) in [
      ("WITH c(x) AS (VALUES(1),(2)) SELECT sum(x) FROM c;", 3),
      ("WITH RECURSIVE c(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM c WHERE x<8) SELECT sum(x) FROM c;", 36),
      ("SELECT x FROM (SELECT 7 AS x);", 7)] do
    let parsed ← match CoreTokenGrammar.parseCertified sql with
      | .ok parsed => pure parsed
      | .error message => fail message
    let some statement := parsed.statements[0]? | fail "missing derived statement"
    match CoreDerivedSQL.executeStatement Core.State.empty statement sql with
    | .error message => fail message
    | .ok (next, results) =>
        unless next.database.tables.isEmpty do fail "derived table escaped its statement"
        let rows := results.flatMap (·.rows)
        let some row := rows[0]? | fail "missing derived row"
        let some cell := row[0]? | fail "missing derived cell"
        match CoreExpr.value cell with
        | .error message => fail message
        | .ok value => unless value == Value.integer expected do fail "wrong derived result"
  let sql := "SELECT x FROM (SELECT 7 AS x);"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed
    | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "missing outer SELECT"
  let forged := { query with sources := query.sources.map fun source =>
    { source with subquerySql := some "SELECT 8 AS x" } }
  match CoreTokenGrammar.check parsed.tokens #[.select forged] with
  | .ok _ => fail "token replay admitted changed captured SQL"
  | .error _ => pure ()

def expectLastInsertRowid : IO Unit := do
  let mut state := Core.State.empty
  for source in SQLite.Script.split "CREATE TABLE t(id INTEGER PRIMARY KEY,v INTEGER); BEGIN; INSERT INTO t VALUES(80,1),(4,2); ROLLBACK;" do
    let parsed ← match CoreTokenGrammar.parseCertified source with
      | .ok parsed => pure parsed
      | .error message => fail message
    for statement in parsed.statements do
      match CoreConnectionSQL.executeStatement state statement source with
      | .error message => fail message
      | .ok (next, _) => state := next
  unless state.lastInsertRowid == 4 do fail "last inserted rowid was reset by rollback"
  let some table := state.database.findTable? "t" | fail "rowid fixture lost table"
  unless table.rows.isEmpty do fail "rowid rollback retained rows"
  let sql := "WITH c(x) AS (VALUES(1),(2)) SELECT last_insert_rowid() FROM c;"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed
    | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing rowid statement"
  match CoreDerivedSQL.executeStatement state statement sql with
  | .error message => fail message
  | .ok (next, results) =>
      unless next.lastInsertRowid == 4 do fail "private materialization overwrote connection rowid"
      for row in results.flatMap (·.rows) do
        let some cell := row[0]? | fail "last_insert_rowid returned no cell"
        match CoreExpr.value cell with
        | .error message => fail message
        | .ok value => unless value == Value.integer 4 do fail "derived query observed an internal rowid"

def expectPragmaTableFunctions : IO Unit := do
  let created ← match CoreSQL.execute Core.State.empty "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);" with
    | .ok value => pure value.1
    | .error message => fail message
  let sql := "SELECT name,arg FROM pragma_table_info('t') ORDER BY cid;"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed
    | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "missing table-function query"
  match CoreDerivedSQL.executeStatement created (.select query) sql with
  | .error message => fail message
  | .ok (next, results) =>
      unless next.database.tables.length == 1 do fail "table-function storage escaped its statement"
      let rows := results.flatMap (·.rows)
      unless rows.length == 2 do fail "table_info row count differs"
      for row in rows do
        let some cell := row[1]? | fail "missing hidden argument"
        match CoreExpr.value cell with
        | .error message => fail message
        | .ok value => unless value == Value.text "t" do fail "wrong hidden argument"
  let forged := { query with sources := query.sources.map fun source =>
    { source with functionArgs := some #[.literal (.text "other")] } }
  match CoreTokenGrammar.check parsed.tokens #[.select forged] with
  | .ok _ => fail "token replay accepted changed table-function arguments"
  | .error _ => pure ()
  match CoreSQL.execute created "SELECT * FROM t(1);" with
  | .ok _ => fail "ordinary table accepted unresolved function arguments"
  | .error _ => pure ()

def expectDerivedInsertInput : IO Unit := do
  let (state, _) ← match CoreSourceSQL.execute Core.State.empty "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);" with
    | .ok result => pure result | .error message => fail message
  let sql := "INSERT INTO t SELECT * FROM (VALUES(1,last_insert_rowid()),(2,last_insert_rowid()));"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok result => pure result | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing derived INSERT"
  let (next, _) ← match CoreDerivedSQL.executeStatement state statement sql with
    | .ok result => pure result | .error message => fail message
  unless next.database.tables.map (·.schema.name) == ["t"] do fail "derived INSERT leaked a private table"
  unless next.lastChanges == 2 && next.totalChanges == 2 && next.lastInsertRowid == 2 do
    fail "derived INSERT changed connection counters incorrectly"
  let (_, output) ← match CoreSQL.execute next "SELECT * FROM t ORDER BY id;" with
    | .ok result => pure result | .error message => fail message
  let expected ← match [[Value.integer 1,.text "0"],[.integer 2,.text "1"]].mapM (List.mapM SQLSurface.value) with
    | .ok result => pure result | .error message => fail message
  unless output.flatMap (·.rows) == expected do fail "derived VALUES lost the per-row insertion register"

def expectZeroLengthDatabase : IO Unit := do
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/zero-length-regression.db"
    journal := ".lake/build/zero-length-regression.db-journal" }
  try
    IO.FS.writeBinFile paths.main ByteArray.empty
    let (database, metadata) ← CoreFileAdapter.reopenWithMetadata paths
    unless database.tables.isEmpty && metadata == {} do fail "zero-length open has unexpected state"
    let header ← CoreFileAdapter.readHeader paths.main
    unless header.databaseSizePages.val == 0 && header.applicationId.val == 0 do
      fail "zero-length open invented persisted header metadata"
    let connection ← CoreFileEngine.reopen .system paths
    match ← CoreFileEngine.execute connection "SELECT 1;" with
    | .error message => fail message | .ok _ => pure ()
    unless (← IO.FS.readBinFile paths.main).isEmpty do fail "read-only open wrote a header"
    match ← CoreFileEngine.execute connection "CREATE TABLE t(x UNIQUE CHECK(x>0));INSERT INTO t VALUES(1);" with
    | .error message => fail message | .ok _ => pure ()
    let database ← CoreFileAdapter.reopen paths
    let some table := database.findTable? "t" | fail "first commit lost the table"
    unless table.rows.length == 1 do fail "first commit lost its row"
  finally
    if ← paths.main.pathExists then IO.FS.removeFile paths.main
    if ← paths.journal.pathExists then IO.FS.removeFile paths.journal

end SQLeanite.Tests
