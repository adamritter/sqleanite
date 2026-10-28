import SQLeaniteTests.UTF16Provenance
import SQLeaniteTests.Fail
import SQLeaniteTests.ExpectSignedIntegerCodec
import SQLeaniteTests.ExpectBoundedPageNumbers
import SQLeaniteTests.ExpectRelationalAlgebra
import SQLeaniteTests.ExpectPhysicalMVPTableBTree
import SQLeaniteTests.ExpectGeneralMVPFileInterop
import SQLeaniteTests.ExpectPhysicalIndexTraversal
import SQLeaniteTests.ExpectWideCIndexCertificate
import SQLeaniteTests.ExpectCoreMultiFreelist
import SQLeaniteTests.ExpectPersistentPageTree
import SQLeaniteTests.ExpectPageSizeConversionFailures
import SQLeaniteTests.ExpectSQLiteQuotedNames
import SQLeaniteTests.ExpectSQLiteAutoIncrement
import SQLeaniteTests.ExpectSQLitePragmaArguments
import SQLeaniteTests.ExpectSQLiteSchemaRename
import SQLeaniteTests.ExpectSQLiteUpdateIgnore
import SQLeaniteTests.ExpectSQLiteMath
import SQLeaniteTests.ExpectSQLiteQuotedFunctions
import SQLeaniteTests.ExpectSQLiteJoinedFixedColumns
import SQLeaniteTests.ExpectSQLiteBetweenCursorPlans
import SQLeaniteTests.ExpectSQLiteJoinRangeTraversal
import SQLeaniteTests.ExpectSQLiteBetweenConstants
import SQLeaniteTests.ExpectSQLiteJoinedNullableData
import SQLeaniteTests.ExpectSQLiteJoinedFixedWhere
import SQLeaniteTests.ExpectSQLiteJoinedDeclaredNullability
import SQLeaniteTests.ExpectSQLiteJoinedNullFilterOrder
import SQLeaniteTests.ExpectSQLiteSingleReadPrefixControls
import SQLeaniteTests.ExpectSQLiteJoinedReadPrefix
import SQLeaniteTests.ExpectSQLiteJoinProjectionWrappers
import SQLeaniteTests.ExpectSQLiteJoinAffinity
import SQLeaniteTests.ExpectSQLiteJoinRangeRegressions
import SQLeaniteTests.JsonValidControlsBatch0
import SQLeaniteTests.JsonValidControlsBatch1
import SQLeaniteTests.JsonValidControlsBatch2
import SQLeaniteTests.ExpectSQLiteJsonSubtype
import SQLeaniteTests.ExpectSQLiteJsonBinaryEscapes
import SQLeaniteTests.ExpectForeignKeyPragmas
import SQLeaniteTests.ExpectCheckAddColumn
import SQLeaniteTests.UnitTestsBatch0
import SQLeaniteTests.UnitTestsBatch1

def main (args : List String) : IO UInt32 := do
  if let ["--wal-index-fixture", walPath, shmPath] := args then
    let frames ← SQLeanite.Tests.expectSQLiteWALIndexFixture walPath shmPath
    IO.println s!"WAL index fixture: {frames} frames, 8 interrupted-append splits"
    return 0
  if let ["--wal-append-fixture", walPath, imagePath, destination] := args then
    let frames ← SQLeanite.Tests.exportSQLiteWALAppend walPath imagePath destination
    IO.println s!"WAL append fixture: {frames} committed frames"
    return 0
  if args == ["--list"] then
    for (name, _) in SQLeanite.Tests.unitTests do IO.println name
    return 0
  let selected ← match args with
    | [] => pure SQLeanite.Tests.unitTests
    | ["--filter", needle] =>
        pure (SQLeanite.Tests.unitTests.filter fun (name, _) => (name.splitOn needle).length > 1)
    | _ => throw (IO.userError "usage: sqleanite_tests [--list | --filter substring]")
  if selected.isEmpty then throw (IO.userError "test filter matched no tests")
  let mut passed := 0
  for (name, test) in selected do
    try
      test
      passed := passed + 1
      IO.println s!"ok - {name}"
    catch e =>
      IO.eprintln s!"not ok - {name}: {e}"
      return 1
  IO.println s!"{passed} SQLeanite tests passed"
  pure 0
