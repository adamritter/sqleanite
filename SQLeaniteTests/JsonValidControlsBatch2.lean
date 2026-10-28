import SQLeaniteTests.ExpectSQLiteJoinAffinity
import SQLeaniteTests.JsonValidControlsBatch0
import SQLeaniteTests.JsonValidControlsBatch1
import TestData.JsonAccessControls.JsonAccessControls0Batch1
import TestData.JsonAccessControls.JsonAccessControls1Batch1
import TestData.JsonAccessControls.JsonAccessControls2Batch1
import TestData.JsonAccessControls.JsonAccessControls3Batch1
import TestData.JsonAccessControls.JsonAccessControls4Batch1
import TestData.JsonAccessControls.JsonAccessControls5Batch1
import TestData.JsonAccessControls.JsonAccessControls6Batch1
import TestData.JsonAccessControls.JsonAccessControls7Batch1
import TestData.JsonAccessControls.JsonAccessControls8
import TestData.JsonPositionControls.JsonPositionControls0
import TestData.JsonPositionControls.JsonPositionControls1
import TestData.JsonPositionControls.JsonPositionControls2
import TestData.JsonPositionControls.JsonPositionControls3
import TestData.PercentileControls.PercentileControls0
import TestData.PercentileControls.PercentileControls1
import TestData.PercentileControls.PercentileControls2
import TestData.PercentileControls.PercentileControls3
import TestData.PercentileControls.PercentileControls4
import TestData.SqliteJsonArrowCases.SqliteJsonArrowCases0
import TestData.SqliteJsonArrowCases.SqliteJsonArrowCases1000
import TestData.SqliteJsonArrowCases.SqliteJsonArrowCases1250
import TestData.SqliteJsonArrowCases.SqliteJsonArrowCases1500
import TestData.SqliteJsonArrowCases.SqliteJsonArrowCases1750
import TestData.SqliteJsonArrowCases.SqliteJsonArrowCases2000
import TestData.SqliteJsonArrowCases.SqliteJsonArrowCases250
import TestData.SqliteJsonArrowCases.SqliteJsonArrowCases500
import TestData.SqliteJsonArrowCases.SqliteJsonArrowCases750
import TestData.SqliteJsonBinaryAdmissionCases
import TestData.SqliteJsonBinaryCases.SqliteJsonBinaryCases0
import TestData.SqliteJsonBinaryCases.SqliteJsonBinaryCases300
import TestData.SqliteJsonBinaryCases.SqliteJsonBinaryCases600
import TestData.SqliteJsonEscapeTailCases.SqliteJsonEscapeTailCases0
import TestData.SqliteJsonEscapeTailCases.SqliteJsonEscapeTailCases400
import TestData.SqliteJsonExtractCases.SqliteJsonExtractCases0
import TestData.SqliteJsonExtractCases.SqliteJsonExtractCases1000
import TestData.SqliteJsonExtractCases.SqliteJsonExtractCases1250
import TestData.SqliteJsonExtractCases.SqliteJsonExtractCases1500
import TestData.SqliteJsonExtractCases.SqliteJsonExtractCases1750
import TestData.SqliteJsonExtractCases.SqliteJsonExtractCases250
import TestData.SqliteJsonExtractCases.SqliteJsonExtractCases500
import TestData.SqliteJsonExtractCases.SqliteJsonExtractCases750
import TestData.SqliteJsonExtractErrorCases
import TestData.SqliteJsonPatchCases.SqliteJsonPatchCases0
import TestData.SqliteJsonPatchCases.SqliteJsonPatchCases1000
import TestData.SqliteJsonPatchCases.SqliteJsonPatchCases1250
import TestData.SqliteJsonPatchCases.SqliteJsonPatchCases1500
import TestData.SqliteJsonPatchCases.SqliteJsonPatchCases1750
import TestData.SqliteJsonPatchCases.SqliteJsonPatchCases2000
import TestData.SqliteJsonPatchCases.SqliteJsonPatchCases2250
import TestData.SqliteJsonPatchCases.SqliteJsonPatchCases250
import TestData.SqliteJsonPatchCases.SqliteJsonPatchCases2500
import TestData.SqliteJsonPatchCases.SqliteJsonPatchCases500
import TestData.SqliteJsonPatchCases.SqliteJsonPatchCases750
import TestData.SqliteJsonPrettyCases.SqliteJsonPrettyCases0
import TestData.SqliteJsonPrettyCases.SqliteJsonPrettyCases1000
import TestData.SqliteJsonPrettyCases.SqliteJsonPrettyCases1250
import TestData.SqliteJsonPrettyCases.SqliteJsonPrettyCases250
import TestData.SqliteJsonPrettyCases.SqliteJsonPrettyCases500
import TestData.SqliteJsonPrettyCases.SqliteJsonPrettyCases750
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases0
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases1000
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases1250
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases1500
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases1750
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases2000
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases2250
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases250
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases2500
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases2750
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases3000
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases500
import TestData.SqliteJsonRemoveCases.SqliteJsonRemoveCases750
import TestData.SqliteJsonTextCases.SqliteJsonTextCases0
import TestData.SqliteJsonTextCases.SqliteJsonTextCases1000
import TestData.SqliteJsonTextCases.SqliteJsonTextCases1250
import TestData.SqliteJsonTextCases.SqliteJsonTextCases1500
import TestData.SqliteJsonTextCases.SqliteJsonTextCases250
import TestData.SqliteJsonTextCases.SqliteJsonTextCases500
import TestData.SqliteJsonTextCases.SqliteJsonTextCases750

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def jsonValidControlsBatch2 : List (String × List Value) := [
    ("X'295c0a'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'395c0d0a'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'495c0a5c61'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'695c0a5c785a5a'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'395c0aff'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'1a5c'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'2a5c61'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'2a5c30'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'3a5c3031'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'2a5c78'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'4a5c783030'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'4a5c784747'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'6a5c7530303030'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'6a5c7547474747'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'2a5c76'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'2a5c27'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'2a5c0a'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'3a5c0d0a'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'4a5c0a5c61'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'6a5c0a5c785a5a'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'3a5c0aff'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'c0'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'c000'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'd00000'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'f00000000100000000'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'cb01'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'cb0200'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'1b00'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'2b0001'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'1c00'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'3c176100'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'3c136100'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'2c1761'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'4c17610000'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'0b00'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'0f'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'31323334'", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'3132333435'", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'5b313233345d'", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'7b2261223a317d'", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'5b305d' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'2b1330'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'5b5b305d5d' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'3b2b1330'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'5b5b5b5b5b5b5b5b5b5b305d5d5d5d5d5d5d5d5d5d' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'bbab9b8b7b6b5b4b3b2b1330'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b305d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'db0b26db0b23db0b20db0b1ddb0b1adb0b17db0b14db0b11db0b0edb0b0bdb0b08db0b05db0b02db0affdb0afcdb0af9db0af6db0af3db0af0db0aeddb0aeadb0ae7db0ae4db0ae1db0adedb0adbdb0ad8db0ad5db0ad2db0acfdb0accdb0ac9db0ac6db0ac3db0ac0db0abddb0abadb0ab7db0ab4db0ab1db0aaedb0aabdb0aa8db0aa5db0aa2db0a9fdb0a9cdb0a99db0a96db0a93db0a90db0a8ddb0a8adb0a87db0a84db0a81db0a7edb0a7bdb0a78db0a75db0a72db0a6fdb0a6cdb0a69db0a66db0a63db0a60db0a5ddb0a5adb0a57db0a54db0a51db0a4edb0a4bdb0a48db0a45db0a42db0a3fdb0a3cdb0a39db0a36db0a33db0a30db0a2ddb0a2adb0a27db0a24db0a21db0a1edb0a1bdb0a18db0a15db0a12db0a0fdb0a0cdb0a09db0a06db0a03db0a00db09fddb09fadb09f7db09f4db09f1db09eedb09ebdb09e8db09e5db09e2db09dfdb09dcdb09d9db09d6db09d3db09d0db09cddb09cadb09c7db09c4db09c1db09bedb09bbdb09b8db09b5db09b2db09afdb09acdb09a9db09a6db09a3db09a0db099ddb099adb0997db0994db0991db098edb098bdb0988db0985db0982db097fdb097cdb0979db0976db0973db0970db096ddb096adb0967db0964db0961db095edb095bdb0958db0955db0952db094fdb094cdb0949db0946db0943db0940db093ddb093adb0937db0934db0931db092edb092bdb0928db0925db0922db091fdb091cdb0919db0916db0913db0910db090ddb090adb0907db0904db0901db08fedb08fbdb08f8db08f5db08f2db08efdb08ecdb08e9db08e6db08e3db08e0db08dddb08dadb08d7db08d4db08d1db08cedb08cbdb08c8db08c5db08c2db08bfdb08bcdb08b9db08b6db08b3db08b0db08addb08aadb08a7db08a4db08a1db089edb089bdb0898db0895db0892db088fdb088cdb0889db0886db0883db0880db087ddb087adb0877db0874db0871db086edb086bdb0868db0865db0862db085fdb085cdb0859db0856db0853db0850db084ddb084adb0847db0844db0841db083edb083bdb0838db0835db0832db082fdb082cdb0829db0826db0823db0820db081ddb081adb0817db0814db0811db080edb080bdb0808db0805db0802db07ffdb07fcdb07f9db07f6db07f3db07f0db07eddb07eadb07e7db07e4db07e1db07dedb07dbdb07d8db07d5db07d2db07cfdb07ccdb07c9db07c6db07c3db07c0db07bddb07badb07b7db07b4db07b1db07aedb07abdb07a8db07a5db07a2db079fdb079cdb0799db0796db0793db0790db078ddb078adb0787db0784db0781db077edb077bdb0778db0775db0772db076fdb076cdb0769db0766db0763db0760db075ddb075adb0757db0754db0751db074edb074bdb0748db0745db0742db073fdb073cdb0739db0736db0733db0730db072ddb072adb0727db0724db0721db071edb071bdb0718db0715db0712db070fdb070cdb0709db0706db0703db0700db06fddb06fadb06f7db06f4db06f1db06eedb06ebdb06e8db06e5db06e2db06dfdb06dcdb06d9db06d6db06d3db06d0db06cddb06cadb06c7db06c4db06c1db06bedb06bbdb06b8db06b5db06b2db06afdb06acdb06a9db06a6db06a3db06a0db069ddb069adb0697db0694db0691db068edb068bdb0688db0685db0682db067fdb067cdb0679db0676db0673db0670db066ddb066adb0667db0664db0661db065edb065bdb0658db0655db0652db064fdb064cdb0649db0646db0643db0640db063ddb063adb0637db0634db0631db062edb062bdb0628db0625db0622db061fdb061cdb0619db0616db0613db0610db060ddb060adb0607db0604db0601db05fedb05fbdb05f8db05f5db05f2db05efdb05ecdb05e9db05e6db05e3db05e0db05dddb05dadb05d7db05d4db05d1db05cedb05cbdb05c8db05c5db05c2db05bfdb05bcdb05b9db05b6db05b3db05b0db05addb05aadb05a7db05a4db05a1db059edb059bdb0598db0595db0592db058fdb058cdb0589db0586db0583db0580db057ddb057adb0577db0574db0571db056edb056bdb0568db0565db0562db055fdb055cdb0559db0556db0553db0550db054ddb054adb0547db0544db0541db053edb053bdb0538db0535db0532db052fdb052cdb0529db0526db0523db0520db051ddb051adb0517db0514db0511db050edb050bdb0508db0505db0502db04ffdb04fcdb04f9db04f6db04f3db04f0db04eddb04eadb04e7db04e4db04e1db04dedb04dbdb04d8db04d5db04d2db04cfdb04ccdb04c9db04c6db04c3db04c0db04bddb04badb04b7db04b4db04b1db04aedb04abdb04a8db04a5db04a2db049fdb049cdb0499db0496db0493db0490db048ddb048adb0487db0484db0481db047edb047bdb0478db0475db0472db046fdb046cdb0469db0466db0463db0460db045ddb045adb0457db0454db0451db044edb044bdb0448db0445db0442db043fdb043cdb0439db0436db0433db0430db042ddb042adb0427db0424db0421db041edb041bdb0418db0415db0412db040fdb040cdb0409db0406db0403db0400db03fddb03fadb03f7db03f4db03f1db03eedb03ebdb03e8db03e5db03e2db03dfdb03dcdb03d9db03d6db03d3db03d0db03cddb03cadb03c7db03c4db03c1db03bedb03bbdb03b8db03b5db03b2db03afdb03acdb03a9db03a6db03a3db03a0db039ddb039adb0397db0394db0391db038edb038bdb0388db0385db0382db037fdb037cdb0379db0376db0373db0370db036ddb036adb0367db0364db0361db035edb035bdb0358db0355db0352db034fdb034cdb0349db0346db0343db0340db033ddb033adb0337db0334db0331db032edb032bdb0328db0325db0322db031fdb031cdb0319db0316db0313db0310db030ddb030adb0307db0304db0301db02fedb02fbdb02f8db02f5db02f2db02efdb02ecdb02e9db02e6db02e3db02e0db02dddb02dadb02d7db02d4db02d1db02cedb02cbdb02c8db02c5db02c2db02bfdb02bcdb02b9db02b6db02b3db02b0db02addb02aadb02a7db02a4db02a1db029edb029bdb0298db0295db0292db028fdb028cdb0289db0286db0283db0280db027ddb027adb0277db0274db0271db026edb026bdb0268db0265db0262db025fdb025cdb0259db0256db0253db0250db024ddb024adb0247db0244db0241db023edb023bdb0238db0235db0232db022fdb022cdb0229db0226db0223db0220db021ddb021adb0217db0214db0211db020edb020bdb0208db0205db0202db01ffdb01fcdb01f9db01f6db01f3db01f0db01eddb01eadb01e7db01e4db01e1db01dedb01dbdb01d8db01d5db01d2db01cfdb01ccdb01c9db01c6db01c3db01c0db01bddb01badb01b7db01b4db01b1db01aedb01abdb01a8db01a5db01a2db019fdb019cdb0199db0196db0193db0190db018ddb018adb0187db0184db0181db017edb017bdb0178db0175db0172db016fdb016cdb0169db0166db0163db0160db015ddb015adb0157db0154db0151db014edb014bdb0148db0145db0142db013fdb013cdb0139db0136db0133db0130db012ddb012adb0127db0124db0121db011edb011bdb0118db0115db0112db010fdb010cdb0109db0106db0103db0100cbfecbfccbfacbf8cbf6cbf4cbf2cbf0cbeecbeccbeacbe8cbe6cbe4cbe2cbe0cbdecbdccbdacbd8cbd6cbd4cbd2cbd0cbcecbcccbcacbc8cbc6cbc4cbc2cbc0cbbecbbccbbacbb8cbb6cbb4cbb2cbb0cbaecbaccbaacba8cba6cba4cba2cba0cb9ecb9ccb9acb98cb96cb94cb92cb90cb8ecb8ccb8acb88cb86cb84cb82cb80cb7ecb7ccb7acb78cb76cb74cb72cb70cb6ecb6ccb6acb68cb66cb64cb62cb60cb5ecb5ccb5acb58cb56cb54cb52cb50cb4ecb4ccb4acb48cb46cb44cb42cb40cb3ecb3ccb3acb38cb36cb34cb32cb30cb2ecb2ccb2acb28cb26cb24cb22cb20cb1ecb1ccb1acb18cb16cb14cb12cb10cb0ecb0cbbab9b8b7b6b5b4b3b2b1330'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b305d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'db0b29db0b26db0b23db0b20db0b1ddb0b1adb0b17db0b14db0b11db0b0edb0b0bdb0b08db0b05db0b02db0affdb0afcdb0af9db0af6db0af3db0af0db0aeddb0aeadb0ae7db0ae4db0ae1db0adedb0adbdb0ad8db0ad5db0ad2db0acfdb0accdb0ac9db0ac6db0ac3db0ac0db0abddb0abadb0ab7db0ab4db0ab1db0aaedb0aabdb0aa8db0aa5db0aa2db0a9fdb0a9cdb0a99db0a96db0a93db0a90db0a8ddb0a8adb0a87db0a84db0a81db0a7edb0a7bdb0a78db0a75db0a72db0a6fdb0a6cdb0a69db0a66db0a63db0a60db0a5ddb0a5adb0a57db0a54db0a51db0a4edb0a4bdb0a48db0a45db0a42db0a3fdb0a3cdb0a39db0a36db0a33db0a30db0a2ddb0a2adb0a27db0a24db0a21db0a1edb0a1bdb0a18db0a15db0a12db0a0fdb0a0cdb0a09db0a06db0a03db0a00db09fddb09fadb09f7db09f4db09f1db09eedb09ebdb09e8db09e5db09e2db09dfdb09dcdb09d9db09d6db09d3db09d0db09cddb09cadb09c7db09c4db09c1db09bedb09bbdb09b8db09b5db09b2db09afdb09acdb09a9db09a6db09a3db09a0db099ddb099adb0997db0994db0991db098edb098bdb0988db0985db0982db097fdb097cdb0979db0976db0973db0970db096ddb096adb0967db0964db0961db095edb095bdb0958db0955db0952db094fdb094cdb0949db0946db0943db0940db093ddb093adb0937db0934db0931db092edb092bdb0928db0925db0922db091fdb091cdb0919db0916db0913db0910db090ddb090adb0907db0904db0901db08fedb08fbdb08f8db08f5db08f2db08efdb08ecdb08e9db08e6db08e3db08e0db08dddb08dadb08d7db08d4db08d1db08cedb08cbdb08c8db08c5db08c2db08bfdb08bcdb08b9db08b6db08b3db08b0db08addb08aadb08a7db08a4db08a1db089edb089bdb0898db0895db0892db088fdb088cdb0889db0886db0883db0880db087ddb087adb0877db0874db0871db086edb086bdb0868db0865db0862db085fdb085cdb0859db0856db0853db0850db084ddb084adb0847db0844db0841db083edb083bdb0838db0835db0832db082fdb082cdb0829db0826db0823db0820db081ddb081adb0817db0814db0811db080edb080bdb0808db0805db0802db07ffdb07fcdb07f9db07f6db07f3db07f0db07eddb07eadb07e7db07e4db07e1db07dedb07dbdb07d8db07d5db07d2db07cfdb07ccdb07c9db07c6db07c3db07c0db07bddb07badb07b7db07b4db07b1db07aedb07abdb07a8db07a5db07a2db079fdb079cdb0799db0796db0793db0790db078ddb078adb0787db0784db0781db077edb077bdb0778db0775db0772db076fdb076cdb0769db0766db0763db0760db075ddb075adb0757db0754db0751db074edb074bdb0748db0745db0742db073fdb073cdb0739db0736db0733db0730db072ddb072adb0727db0724db0721db071edb071bdb0718db0715db0712db070fdb070cdb0709db0706db0703db0700db06fddb06fadb06f7db06f4db06f1db06eedb06ebdb06e8db06e5db06e2db06dfdb06dcdb06d9db06d6db06d3db06d0db06cddb06cadb06c7db06c4db06c1db06bedb06bbdb06b8db06b5db06b2db06afdb06acdb06a9db06a6db06a3db06a0db069ddb069adb0697db0694db0691db068edb068bdb0688db0685db0682db067fdb067cdb0679db0676db0673db0670db066ddb066adb0667db0664db0661db065edb065bdb0658db0655db0652db064fdb064cdb0649db0646db0643db0640db063ddb063adb0637db0634db0631db062edb062bdb0628db0625db0622db061fdb061cdb0619db0616db0613db0610db060ddb060adb0607db0604db0601db05fedb05fbdb05f8db05f5db05f2db05efdb05ecdb05e9db05e6db05e3db05e0db05dddb05dadb05d7db05d4db05d1db05cedb05cbdb05c8db05c5db05c2db05bfdb05bcdb05b9db05b6db05b3db05b0db05addb05aadb05a7db05a4db05a1db059edb059bdb0598db0595db0592db058fdb058cdb0589db0586db0583db0580db057ddb057adb0577db0574db0571db056edb056bdb0568db0565db0562db055fdb055cdb0559db0556db0553db0550db054ddb054adb0547db0544db0541db053edb053bdb0538db0535db0532db052fdb052cdb0529db0526db0523db0520db051ddb051adb0517db0514db0511db050edb050bdb0508db0505db0502db04ffdb04fcdb04f9db04f6db04f3db04f0db04eddb04eadb04e7db04e4db04e1db04dedb04dbdb04d8db04d5db04d2db04cfdb04ccdb04c9db04c6db04c3db04c0db04bddb04badb04b7db04b4db04b1db04aedb04abdb04a8db04a5db04a2db049fdb049cdb0499db0496db0493db0490db048ddb048adb0487db0484db0481db047edb047bdb0478db0475db0472db046fdb046cdb0469db0466db0463db0460db045ddb045adb0457db0454db0451db044edb044bdb0448db0445db0442db043fdb043cdb0439db0436db0433db0430db042ddb042adb0427db0424db0421db041edb041bdb0418db0415db0412db040fdb040cdb0409db0406db0403db0400db03fddb03fadb03f7db03f4db03f1db03eedb03ebdb03e8db03e5db03e2db03dfdb03dcdb03d9db03d6db03d3db03d0db03cddb03cadb03c7db03c4db03c1db03bedb03bbdb03b8db03b5db03b2db03afdb03acdb03a9db03a6db03a3db03a0db039ddb039adb0397db0394db0391db038edb038bdb0388db0385db0382db037fdb037cdb0379db0376db0373db0370db036ddb036adb0367db0364db0361db035edb035bdb0358db0355db0352db034fdb034cdb0349db0346db0343db0340db033ddb033adb0337db0334db0331db032edb032bdb0328db0325db0322db031fdb031cdb0319db0316db0313db0310db030ddb030adb0307db0304db0301db02fedb02fbdb02f8db02f5db02f2db02efdb02ecdb02e9db02e6db02e3db02e0db02dddb02dadb02d7db02d4db02d1db02cedb02cbdb02c8db02c5db02c2db02bfdb02bcdb02b9db02b6db02b3db02b0db02addb02aadb02a7db02a4db02a1db029edb029bdb0298db0295db0292db028fdb028cdb0289db0286db0283db0280db027ddb027adb0277db0274db0271db026edb026bdb0268db0265db0262db025fdb025cdb0259db0256db0253db0250db024ddb024adb0247db0244db0241db023edb023bdb0238db0235db0232db022fdb022cdb0229db0226db0223db0220db021ddb021adb0217db0214db0211db020edb020bdb0208db0205db0202db01ffdb01fcdb01f9db01f6db01f3db01f0db01eddb01eadb01e7db01e4db01e1db01dedb01dbdb01d8db01d5db01d2db01cfdb01ccdb01c9db01c6db01c3db01c0db01bddb01badb01b7db01b4db01b1db01aedb01abdb01a8db01a5db01a2db019fdb019cdb0199db0196db0193db0190db018ddb018adb0187db0184db0181db017edb017bdb0178db0175db0172db016fdb016cdb0169db0166db0163db0160db015ddb015adb0157db0154db0151db014edb014bdb0148db0145db0142db013fdb013cdb0139db0136db0133db0130db012ddb012adb0127db0124db0121db011edb011bdb0118db0115db0112db010fdb010cdb0109db0106db0103db0100cbfecbfccbfacbf8cbf6cbf4cbf2cbf0cbeecbeccbeacbe8cbe6cbe4cbe2cbe0cbdecbdccbdacbd8cbd6cbd4cbd2cbd0cbcecbcccbcacbc8cbc6cbc4cbc2cbc0cbbecbbccbbacbb8cbb6cbb4cbb2cbb0cbaecbaccbaacba8cba6cba4cba2cba0cb9ecb9ccb9acb98cb96cb94cb92cb90cb8ecb8ccb8acb88cb86cb84cb82cb80cb7ecb7ccb7acb78cb76cb74cb72cb70cb6ecb6ccb6acb68cb66cb64cb62cb60cb5ecb5ccb5acb58cb56cb54cb52cb50cb4ecb4ccb4acb48cb46cb44cb42cb40cb3ecb3ccb3acb38cb36cb34cb32cb30cb2ecb2ccb2acb28cb26cb24cb22cb20cb1ecb1ccb1acb18cb16cb14cb12cb10cb0ecb0cbbab9b8b7b6b5b4b3b2b1330'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b305d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'db0b2cdb0b29db0b26db0b23db0b20db0b1ddb0b1adb0b17db0b14db0b11db0b0edb0b0bdb0b08db0b05db0b02db0affdb0afcdb0af9db0af6db0af3db0af0db0aeddb0aeadb0ae7db0ae4db0ae1db0adedb0adbdb0ad8db0ad5db0ad2db0acfdb0accdb0ac9db0ac6db0ac3db0ac0db0abddb0abadb0ab7db0ab4db0ab1db0aaedb0aabdb0aa8db0aa5db0aa2db0a9fdb0a9cdb0a99db0a96db0a93db0a90db0a8ddb0a8adb0a87db0a84db0a81db0a7edb0a7bdb0a78db0a75db0a72db0a6fdb0a6cdb0a69db0a66db0a63db0a60db0a5ddb0a5adb0a57db0a54db0a51db0a4edb0a4bdb0a48db0a45db0a42db0a3fdb0a3cdb0a39db0a36db0a33db0a30db0a2ddb0a2adb0a27db0a24db0a21db0a1edb0a1bdb0a18db0a15db0a12db0a0fdb0a0cdb0a09db0a06db0a03db0a00db09fddb09fadb09f7db09f4db09f1db09eedb09ebdb09e8db09e5db09e2db09dfdb09dcdb09d9db09d6db09d3db09d0db09cddb09cadb09c7db09c4db09c1db09bedb09bbdb09b8db09b5db09b2db09afdb09acdb09a9db09a6db09a3db09a0db099ddb099adb0997db0994db0991db098edb098bdb0988db0985db0982db097fdb097cdb0979db0976db0973db0970db096ddb096adb0967db0964db0961db095edb095bdb0958db0955db0952db094fdb094cdb0949db0946db0943db0940db093ddb093adb0937db0934db0931db092edb092bdb0928db0925db0922db091fdb091cdb0919db0916db0913db0910db090ddb090adb0907db0904db0901db08fedb08fbdb08f8db08f5db08f2db08efdb08ecdb08e9db08e6db08e3db08e0db08dddb08dadb08d7db08d4db08d1db08cedb08cbdb08c8db08c5db08c2db08bfdb08bcdb08b9db08b6db08b3db08b0db08addb08aadb08a7db08a4db08a1db089edb089bdb0898db0895db0892db088fdb088cdb0889db0886db0883db0880db087ddb087adb0877db0874db0871db086edb086bdb0868db0865db0862db085fdb085cdb0859db0856db0853db0850db084ddb084adb0847db0844db0841db083edb083bdb0838db0835db0832db082fdb082cdb0829db0826db0823db0820db081ddb081adb0817db0814db0811db080edb080bdb0808db0805db0802db07ffdb07fcdb07f9db07f6db07f3db07f0db07eddb07eadb07e7db07e4db07e1db07dedb07dbdb07d8db07d5db07d2db07cfdb07ccdb07c9db07c6db07c3db07c0db07bddb07badb07b7db07b4db07b1db07aedb07abdb07a8db07a5db07a2db079fdb079cdb0799db0796db0793db0790db078ddb078adb0787db0784db0781db077edb077bdb0778db0775db0772db076fdb076cdb0769db0766db0763db0760db075ddb075adb0757db0754db0751db074edb074bdb0748db0745db0742db073fdb073cdb0739db0736db0733db0730db072ddb072adb0727db0724db0721db071edb071bdb0718db0715db0712db070fdb070cdb0709db0706db0703db0700db06fddb06fadb06f7db06f4db06f1db06eedb06ebdb06e8db06e5db06e2db06dfdb06dcdb06d9db06d6db06d3db06d0db06cddb06cadb06c7db06c4db06c1db06bedb06bbdb06b8db06b5db06b2db06afdb06acdb06a9db06a6db06a3db06a0db069ddb069adb0697db0694db0691db068edb068bdb0688db0685db0682db067fdb067cdb0679db0676db0673db0670db066ddb066adb0667db0664db0661db065edb065bdb0658db0655db0652db064fdb064cdb0649db0646db0643db0640db063ddb063adb0637db0634db0631db062edb062bdb0628db0625db0622db061fdb061cdb0619db0616db0613db0610db060ddb060adb0607db0604db0601db05fedb05fbdb05f8db05f5db05f2db05efdb05ecdb05e9db05e6db05e3db05e0db05dddb05dadb05d7db05d4db05d1db05cedb05cbdb05c8db05c5db05c2db05bfdb05bcdb05b9db05b6db05b3db05b0db05addb05aadb05a7db05a4db05a1db059edb059bdb0598db0595db0592db058fdb058cdb0589db0586db0583db0580db057ddb057adb0577db0574db0571db056edb056bdb0568db0565db0562db055fdb055cdb0559db0556db0553db0550db054ddb054adb0547db0544db0541db053edb053bdb0538db0535db0532db052fdb052cdb0529db0526db0523db0520db051ddb051adb0517db0514db0511db050edb050bdb0508db0505db0502db04ffdb04fcdb04f9db04f6db04f3db04f0db04eddb04eadb04e7db04e4db04e1db04dedb04dbdb04d8db04d5db04d2db04cfdb04ccdb04c9db04c6db04c3db04c0db04bddb04badb04b7db04b4db04b1db04aedb04abdb04a8db04a5db04a2db049fdb049cdb0499db0496db0493db0490db048ddb048adb0487db0484db0481db047edb047bdb0478db0475db0472db046fdb046cdb0469db0466db0463db0460db045ddb045adb0457db0454db0451db044edb044bdb0448db0445db0442db043fdb043cdb0439db0436db0433db0430db042ddb042adb0427db0424db0421db041edb041bdb0418db0415db0412db040fdb040cdb0409db0406db0403db0400db03fddb03fadb03f7db03f4db03f1db03eedb03ebdb03e8db03e5db03e2db03dfdb03dcdb03d9db03d6db03d3db03d0db03cddb03cadb03c7db03c4db03c1db03bedb03bbdb03b8db03b5db03b2db03afdb03acdb03a9db03a6db03a3db03a0db039ddb039adb0397db0394db0391db038edb038bdb0388db0385db0382db037fdb037cdb0379db0376db0373db0370db036ddb036adb0367db0364db0361db035edb035bdb0358db0355db0352db034fdb034cdb0349db0346db0343db0340db033ddb033adb0337db0334db0331db032edb032bdb0328db0325db0322db031fdb031cdb0319db0316db0313db0310db030ddb030adb0307db0304db0301db02fedb02fbdb02f8db02f5db02f2db02efdb02ecdb02e9db02e6db02e3db02e0db02dddb02dadb02d7db02d4db02d1db02cedb02cbdb02c8db02c5db02c2db02bfdb02bcdb02b9db02b6db02b3db02b0db02addb02aadb02a7db02a4db02a1db029edb029bdb0298db0295db0292db028fdb028cdb0289db0286db0283db0280db027ddb027adb0277db0274db0271db026edb026bdb0268db0265db0262db025fdb025cdb0259db0256db0253db0250db024ddb024adb0247db0244db0241db023edb023bdb0238db0235db0232db022fdb022cdb0229db0226db0223db0220db021ddb021adb0217db0214db0211db020edb020bdb0208db0205db0202db01ffdb01fcdb01f9db01f6db01f3db01f0db01eddb01eadb01e7db01e4db01e1db01dedb01dbdb01d8db01d5db01d2db01cfdb01ccdb01c9db01c6db01c3db01c0db01bddb01badb01b7db01b4db01b1db01aedb01abdb01a8db01a5db01a2db019fdb019cdb0199db0196db0193db0190db018ddb018adb0187db0184db0181db017edb017bdb0178db0175db0172db016fdb016cdb0169db0166db0163db0160db015ddb015adb0157db0154db0151db014edb014bdb0148db0145db0142db013fdb013cdb0139db0136db0133db0130db012ddb012adb0127db0124db0121db011edb011bdb0118db0115db0112db010fdb010cdb0109db0106db0103db0100cbfecbfccbfacbf8cbf6cbf4cbf2cbf0cbeecbeccbeacbe8cbe6cbe4cbe2cbe0cbdecbdccbdacbd8cbd6cbd4cbd2cbd0cbcecbcccbcacbc8cbc6cbc4cbc2cbc0cbbecbbccbbacbb8cbb6cbb4cbb2cbb0cbaecbaccbaacba8cba6cba4cba2cba0cb9ecb9ccb9acb98cb96cb94cb92cb90cb8ecb8ccb8acb88cb86cb84cb82cb80cb7ecb7ccb7acb78cb76cb74cb72cb70cb6ecb6ccb6acb68cb66cb64cb62cb60cb5ecb5ccb5acb58cb56cb54cb52cb50cb4ecb4ccb4acb48cb46cb44cb42cb40cb3ecb3ccb3acb38cb36cb34cb32cb30cb2ecb2ccb2acb28cb26cb24cb22cb20cb1ecb1ccb1acb18cb16cb14cb12cb10cb0ecb0cbbab9b8b7b6b5b4b3b2b1330'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("NULL", [.null, .null, .null, .null, .null, .null, .null, .null, .null, .null, .null, .null, .null, .null, .null, .null]),
    ("0", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("1", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("-1", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("1.5", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("1e99", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("-1e999", [.integer 0, .integer 0, .integer 1, .integer 1, .integer 0, .integer 0, .integer 1, .integer 1, .integer 0, .integer 0, .integer 1, .integer 1, .integer 0, .integer 0, .integer 1, .integer 1]),
    ("9223372036854775807", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'66616c7365' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'02'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'66616c65' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X''", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'99852439b62717d271093f'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'74727565' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'01'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'747275ab' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'0125'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'19'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'2222' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'07'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'9d2222' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'07'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'9d51dfac'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'32363630363633303838302e333135333432' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'c51232363630363633303838302e333135333432'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'3236363036363330383830972e333135333432' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'c51232363630363633303838302e3135333432'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'107eaf9ea5a47d578842a3ef2906cf3402468ee335a419'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'225c6e33316231e4b8ad32315c5c6132623230325c22e4b8ade4b8ad5c2222' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'c81d5c6e33316231e4b8ad32315c5c6132623230325c22e4b8ade4b8ad5c22'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'225c6e33316231e4b8ad32315c5c613262323032f85c22e4ade4b8ad5c2222' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'c81d5c6e33316231e4b8ad32315c5c6132623230325c9be4b8ade4b8ad5c22'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'c8efc22cf53b17ee5294960076f63355dc50d6bf3dd27d1f'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'5b5d' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'0b'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'5b5d' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'0b62'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'a3f11179289bae3ed6'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'2d343633333835373237393938313230353939' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'c3132d343633333835373237393938313230353939'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'2d3436333338353732372c3938313230353939' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'c3132d34a933333835373237393938313230353939'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'1a8731834f12cbf5639cc9'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'6e756c6c' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'00'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'6e756cfd24' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'00'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'7a145637dde993898b7c5bd1eeb77963fdd2258f4a'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'74727565' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'01'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'ae7472757465' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'01'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'901c90b177a501f5b1e80ab775'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'22325c743322' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'48325c7433'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'22325c749e22' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'eb48325c7433'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'c841'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'66616c7365' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'02'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'66616c65' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'02'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'90982e6bee0876eac8f221ce998b5bcd'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'74727565' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'01'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'd17565' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'35'", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'ee251fdb6bd6'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'6e756c6c' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'00'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'6e756c' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'000d'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'd1dc60e2ca84d7'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'2d3330363730313636383336313738373231' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'c3122d3330363730313636383336313738373231'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'2d333036373031363638333631373899373231' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'c3122d3330363730313636385436313738373231'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'cfbfc711c809c46c5a8ee672888af319409fa036'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'74727565' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'01'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'74727565df' AS TEXT)", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X''", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("X'9b47bb0af3847a8542e7f3542b9f01250479ec22d8'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0]),
    ("CAST(X'5b22315c75303065395c75303065395c225c5c5c75643833645c7564653030313330222c6e756c6c2c66616c73655d' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'cb24c820315c75303065395c75303065395c225c5c5c75643833645c75646530303133300002'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("CAST(X'5b223175303065395c75303065395c225c5c5c75643833645c7564653030e63330222c6e756c6c2c66616c73655d' AS TEXT)", [.integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 1]),
    ("X'cb24c820315c75303065395c75303065395c225c5c5c75643833645c753b6530303133300002'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1, .integer 0, .integer 0, .integer 0, .integer 0, .integer 1, .integer 1, .integer 1, .integer 1]),
    ("X'191736617973'", [.integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0, .integer 0])
]

def jsonValidControls : List (String × List Value) := jsonValidControlsBatch0 ++ jsonValidControlsBatch1 ++ jsonValidControlsBatch2

def expectSQLiteJsonValid : IO Unit := do
  -- 840 pinned C controls: all valid masks plus the one-argument default.
  -- The full oracle, source inputs and seeded fixture generation are retained.
  let cases := jsonValidControls
  for (expression, expected) in cases do
    let fields := ["json_valid(v)"] ++ (List.range 15).map (fun index => s!"json_valid(v,{index+1})")
    let sql := s!"CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,{expression});SELECT {String.intercalate "," fields} FROM t;"
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"JSON validity {expression}: {message}"
    let wanted ← match expected.mapM SQLSurface.value with
      | .ok row => pure row
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [wanted] do
      fail s!"JSON validity differs from C: {expression}"
  for sql in ["SELECT json_valid(NULL,0);", "SELECT json_valid('1',16);",
      "SELECT json_valid(X'00',NULL);"] do
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless message == "FLAGS parameter to json_valid() must be between 1 and 15" do
        fail s!"JSON mask error: {message}"
    | .ok _ => fail s!"JSON invalid mask admitted: {sql}"
  for sql in ["SELECT json_valid();", "SELECT json_valid(1,2,3) LIMIT 0;",
      "SELECT CASE WHEN 0 THEN json_valid() ELSE 1 END;",
      "CREATE TABLE e(id INTEGER PRIMARY KEY);SELECT json_valid() FROM e;",
      "CREATE TABLE e(id INTEGER PRIMARY KEY);SELECT json_valid(1,2,3) FROM e LIMIT 0;"] do
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless message == "wrong number of arguments to function json_valid()" do
        fail s!"JSON arity error: {message}"
    | .ok _ => fail s!"JSON invalid arity admitted: {sql}"

def expectSQLiteJsonPreparationErrors : IO Unit := do
  let cases : List (String × String) := [
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT JSON_VALID();","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT \"JSON_VALID\"();","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT JsOn_VaLiD(1,2,3);","wrong number of arguments to function JsOn_VaLiD()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT json_valid(*);","wrong number of arguments to function json_valid()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT JSON_VALID(DISTINCT 1,2,3);","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT 0 AND json_valid();","wrong number of arguments to function json_valid()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT json_valid() AND 0;","wrong number of arguments to function json_valid()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT 1 OR json_valid();","wrong number of arguments to function json_valid()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT iif(0,json_valid(),1);","wrong number of arguments to function json_valid()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT CASE WHEN 0 THEN JSON_VALID() ELSE 1 END;","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT JSON_VALID() FROM t LIMIT 0;","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT id FROM t WHERE 0 AND JSON_VALID();","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT sum(JSON_VALID()) FROM t;","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT count(*) FILTER(WHERE JSON_VALID()) FROM t;","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT JSON_VALID() FROM t a JOIN t b USING(id);","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT JSON_VALID() FROM t a JOIN t b USING(id) LIMIT 0;","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT count(*) FROM t ORDER BY JSON_VALID();","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);UPDATE t SET v=JSON_VALID() WHERE 0;","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);INSERT INTO t SELECT 2,JSON_VALID() WHERE 0;","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT json_valid(abs(-9223372036854775808),0);","integer overflow"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT 1 IN (JSON_VALID());","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT 1 NOT IN (JSON_VALID());","wrong number of arguments to function JSON_VALID()"),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1);SELECT id FROM t WHERE id IN (JSON_VALID());","wrong number of arguments to function JSON_VALID()")]
  for (sql, expected) in cases do
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless message == expected do fail s!"JSON preparation differs: {sql}: {message}"
    | .ok _ => fail s!"JSON preparation admitted invalid call: {sql}"

def expectSQLiteJsonAccess : IO Unit := do
  -- 5,343 pinned C controls; the original component diagnostics and all inputs
  -- are retained separately from production executable evaluations.
  let cases := jsonAccessControls0 ++ jsonAccessControls1 ++ jsonAccessControls2 ++ jsonAccessControls3 ++ jsonAccessControls4 ++ jsonAccessControls5 ++ jsonAccessControls6 ++ jsonAccessControls7 ++ jsonAccessControls8
  for (sql, expected, expectedError) in cases do
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless expectedError == some message do fail s!"JSON access error differs: {sql}: {message}"
    | .ok (_, results) =>
        if expectedError.isSome then fail s!"JSON access unexpectedly succeeded: {sql}"
        let wanted ← match expected.mapM SQLSurface.value with
          | .ok row => pure row
          | .error message => fail message
        unless (results.getLast?).map (·.rows) == some [wanted] do
          fail s!"JSON access differs from C: {sql}"

def expectSQLiteByteDiagnostics : IO Unit := do
  -- All 65,536 two-byte strings exercise lossless diagnostic transport,
  -- including malformed UTF-8 and embedded NUL. This is a component control.
  for high in [0:256] do
    for low in [0:256] do
      let data := #[UInt8.ofNat high, UInt8.ofNat low]
      unless SQLite.Diagnostic.bytes (SQLite.Diagnostic.ofBytes data) == data do
        fail "diagnostic byte roundtrip"
  let marker := SQLite.Diagnostic.envelope.toUTF8.data
  unless SQLite.Diagnostic.bytes (SQLite.Diagnostic.ofBytes marker) == marker do
    fail "diagnostic envelope collision"
  for fn in ["json_type", "json_array_length"] do
    let sql := "SELECT " ++ fn ++ "('0',CAST(X'24ff' AS TEXT));"
    match CoreSQL.execute Core.State.empty sql with
    | .error message =>
        unless SQLite.Diagnostic.bytes message == "bad JSON path: '$".toUTF8.data ++ #[255,39] do
          fail "JSON path diagnostic lost invalid UTF-8"
    | .ok _ => fail "invalid JSON path was admitted"

def expectSQLiteIdenticalUpdates : IO Unit := do
  let cases : List (String × String × Bool) := [
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);", "UPDATE t SET v=v;", true),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);", "UPDATE t SET v=NULL WHERE id=1;", true),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);", "UPDATE t SET w=w;", true),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);", "UPDATE t SET id=id;", false),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);", "UPDATE t SET v=v RETURNING id;", true),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);", "UPDATE t SET v=v WHERE 0;", true),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE INDEX ix ON t(v);", "UPDATE t SET v=v;", false),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE INDEX ix ON t(v);", "UPDATE t SET v=NULL WHERE id=1;", false),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE INDEX ix ON t(v);", "UPDATE t SET w=w;", true),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE INDEX ix ON t(v);", "UPDATE t SET id=id;", false),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE INDEX ix ON t(v);", "UPDATE t SET v=v RETURNING id;", false),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE INDEX ix ON t(v);", "UPDATE t SET v=v WHERE 0;", true),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE UNIQUE INDEX ix ON t(v);", "UPDATE t SET v=v;", false),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE UNIQUE INDEX ix ON t(v);", "UPDATE t SET v=NULL WHERE id=1;", false),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE UNIQUE INDEX ix ON t(v);", "UPDATE t SET w=w;", true),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE UNIQUE INDEX ix ON t(v);", "UPDATE t SET id=id;", false),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE UNIQUE INDEX ix ON t(v);", "UPDATE t SET v=v RETURNING id;", false),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE UNIQUE INDEX ix ON t(v);", "UPDATE t SET v=v WHERE 0;", true),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE INDEX ix ON t(w);", "UPDATE t SET v=v;", true),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE INDEX ix ON t(w);", "UPDATE t SET v=NULL WHERE id=1;", true),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE INDEX ix ON t(w);", "UPDATE t SET w=w;", false),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE INDEX ix ON t(w);", "UPDATE t SET id=id;", false),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE INDEX ix ON t(w);", "UPDATE t SET v=v RETURNING id;", true),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v,w);INSERT INTO t VALUES(1,NULL,1),(2,2,2);CREATE INDEX ix ON t(w);", "UPDATE t SET v=v WHERE 0;", true)]
  for (setup, sql, unchanged) in cases do
    let (before, _) ← match CoreSQL.execute Core.State.empty setup with
      | .ok x => pure x | .error message => fail message
    let statements ← match CoreTokenGrammar.parseStatements sql with
      | .ok x => pure x | .error message => fail message
    let statement ← match statements[0]? with
      | some statement => pure statement | none => fail "missing UPDATE statement"
    let (after, results) ← match CoreSQL.executeStatement before statement with
      | .ok x => pure x | .error message => fail message
    unless CoreFileEngine.dataWriteNoop before after statement results == unchanged do
      fail s!"identical UPDATE publication disagrees with C: {setup} {sql}"

def expectSQLiteJsonPosition : IO Unit := do
  -- Pinned C component controls cover text position accounting, malformed binary
  -- headers/payloads, JSON5, depth limits, NULL and all one-byte blobs.
  let cases := jsonPositionControls0 ++ jsonPositionControls1 ++ jsonPositionControls2 ++ jsonPositionControls3
  for (sql, expected) in cases do
    let wanted ← match SQLSurface.value expected with
      | .ok value => pure value | .error message => fail message
    match CoreSQL.execute Core.State.empty sql with
    | .error message => fail s!"JSON position failed: {sql}: {message}"
    | .ok (_, results) =>
        unless (results.getLast?).map (·.rows) == some [[wanted]] do
          fail s!"JSON position differs from C: {sql}"

def expectSQLitePercentile : IO Unit := do
  -- Pinned C controls include all eight interpolation-rounding failures from
  -- the initial standalone component and invalid fraction/data precedence.
  let cases := percentileControls0 ++ percentileControls1 ++ percentileControls2 ++ percentileControls3 ++ percentileControls4
  for (sql, outputs, expectedError) in cases do
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless expectedError == some message do fail s!"percentile error differs: {sql}: {message}"
    | .ok (_, results) =>
        if expectedError.isSome then fail s!"percentile unexpectedly succeeded: {sql}"
        let expected ← match outputs.mapM (fun s => SQLSurface.value (.text s)) with
          | .ok values => pure values | .error message => fail message
        unless (results.getLast?).map (·.rows) == some [expected] do
          fail s!"percentile result differs from C: {sql}"

def expectSQLiteJsonBinary : IO Unit := do
  for (input, expected) in (sqliteJsonBinaryCases0 ++ sqliteJsonBinaryCases300 ++ sqliteJsonBinaryCases600 ++ sqliteJsonBinaryCases900) do
    let sql := "SELECT quote(jsonb(" ++ input ++ "));"
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless expected == "error:" ++ message do
        fail s!"jsonb error differs: {sql}: {message}"
    | .ok (_, results) =>
        let value ← match SQLSurface.value (.text expected) with
          | .ok value => pure value | .error message => fail message
        unless results.getLast?.map (·.rows) == some [[value]] do
          fail s!"jsonb encoding differs: {sql}"

  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,valid);CREATE TABLE out(id INTEGER PRIMARY KEY,valid);"
  for (sql, expected) in sqliteJsonBinaryAdmissionCases do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .error message => unless message == expected do
        fail s!"jsonb admission differs: {sql}: {message}"
    | .ok _ => fail s!"jsonb accepted invalid argument count: {sql}"

def expectSQLiteJsonPretty : IO Unit := do
  for (arguments, expected) in (sqliteJsonPrettyCases0 ++ sqliteJsonPrettyCases250 ++ sqliteJsonPrettyCases500 ++ sqliteJsonPrettyCases750 ++ sqliteJsonPrettyCases1000 ++ sqliteJsonPrettyCases1250) do
    let sql := "SELECT typeof(json_pretty(" ++ arguments ++ ")),hex(json_pretty(" ++ arguments ++ "));"
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless expected == "error:" ++ message do
        fail s!"json_pretty error differs: {sql}: {message}"
    | .ok (_, results) =>
        let fields := expected.splitOn "|"
        let values ← fields.mapM fun field => match SQLSurface.value (.text field) with
          | .ok value => pure value | .error message => fail message
        unless results.getLast?.map (·.rows) == some [values] do
          fail s!"json_pretty rendering differs: {sql}"

def expectSQLiteJsonExtract : IO Unit := do
  for (arguments, expected) in (sqliteJsonExtractCases0 ++ sqliteJsonExtractCases250 ++ sqliteJsonExtractCases500 ++ sqliteJsonExtractCases750 ++ sqliteJsonExtractCases1000 ++ sqliteJsonExtractCases1250 ++ sqliteJsonExtractCases1500 ++ sqliteJsonExtractCases1750 ++ sqliteJsonExtractCases2000) do
    let sql := "SELECT typeof(jsonb_extract(" ++ arguments ++ ")),hex(quote(jsonb_extract(" ++ arguments ++ ")));"
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless expected == "error:" ++ SQLite.Text.hexBytes (SQLite.Diagnostic.bytes message) do
        fail s!"jsonb_extract error differs: {sql}: {message}"
    | .ok (_, results) =>
        let values ← (expected.splitOn "|").mapM fun field => match SQLSurface.value (.text field) with
          | .ok value => pure value | .error message => fail message
        unless results.getLast?.map (·.rows) == some [values] do
          fail s!"jsonb_extract result differs: {sql}"

def expectSQLiteJsonExtractErrors : IO Unit := do
  for (sql, expected) in sqliteJsonExtractErrorCases do
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless expected == "error:" ++ SQLite.Text.hexBytes (SQLite.Diagnostic.bytes message) do
        fail s!"jsonb_extract error order differs: {message}"
    | .ok (_, results) =>
        let values ← (expected.splitOn "|").mapM fun field => match SQLSurface.value (.text field) with
          | .ok value => pure value | .error message => fail message
        unless results.getLast?.map (·.rows) == some [values] do
          fail "jsonb_extract deferred error result differs"
  let setup := "CREATE TABLE t(a,b); INSERT INTO t VALUES(1,2);"
  for name in ["jsonb_extract", "JSONB_EXTRACT", "char", "coalesce"] do
    let call := name ++ "(" ++ String.intercalate "," (List.replicate 1001 "1") ++ ")"
    for value in [call, "(" ++ call ++ ")", "((" ++ call ++ "))", "(" ++ call ++ ",2)", "(2," ++ call ++ ")"] do
      let names := if value.endsWith ",2)" || value.startsWith "(2," then "(a,b)" else "a"
      let sql := setup ++ "UPDATE t SET " ++ names ++ "=" ++ value ++ " WHERE 0;"
      match CoreSQL.execute Core.State.empty sql with
      | .error message => unless message == "too many arguments on function " ++ name do
          fail s!"assignment replaced function limit error: {message}"
      | .ok _ => fail "assignment admitted excessive function arguments"

def expectSQLiteJsonArrow : IO Unit := do
  for (expression, expected) in (sqliteJsonArrowCases0 ++ sqliteJsonArrowCases250 ++ sqliteJsonArrowCases500 ++ sqliteJsonArrowCases750 ++ sqliteJsonArrowCases1000 ++ sqliteJsonArrowCases1250 ++ sqliteJsonArrowCases1500 ++ sqliteJsonArrowCases1750 ++ sqliteJsonArrowCases2000 ++ sqliteJsonArrowCases2250) do
    let sql := "SELECT typeof(" ++ expression ++ "),hex(" ++ expression ++ "),hex(quote(" ++ expression ++ "));"
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless expected == "error:" ++ SQLite.Text.hexBytes (SQLite.Diagnostic.bytes message) do
        fail s!"JSON ->> error differs: {sql}: {message}"
    | .ok (_, results) =>
        let values ← (expected.splitOn "|").mapM fun field => match SQLSurface.value (.text field) with
          | .ok value => pure value | .error message => fail message
        unless results.getLast?.map (·.rows) == some [values] do
          fail s!"JSON ->> value differs: {sql}"

def expectSQLiteQuotedFunctionLimits : IO Unit := do
  for name in ["\"->>\"", "[->>]", "`->>`", "\"char\"", "[char]", "`char`", "\"a\"\"b\"", "`a``b`", "\"CoAlEsCe\""] do
    let call := name ++ "(" ++ String.intercalate "," (List.replicate 1001 "1") ++ ")"
    let scripts := ["SELECT " ++ call ++ ";",
      "SELECT CASE WHEN 0 THEN " ++ call ++ " ELSE 1 END;",
      "CREATE TABLE t(a,b); UPDATE t SET a=" ++ call ++ " WHERE 0;",
      "CREATE TABLE t(a,b); UPDATE t SET a=((" ++ call ++ ")) WHERE 0;",
      "CREATE TABLE t(a,b); UPDATE t SET (a,b)=(1," ++ call ++ ") WHERE 0;"]
    for sql in scripts do
      match CoreSQL.execute Core.State.empty sql with
      | .error message => unless message == "too many arguments on function " ++ name do
          fail s!"quoted function limit spelling differs: {message}"
      | .ok _ => fail "quoted function limit accepted excessive arguments"

def expectSQLiteJsonEscapeTail : IO Unit := do
  for (sql, expected) in (sqliteJsonEscapeTailCases0 ++ sqliteJsonEscapeTailCases200 ++ sqliteJsonEscapeTailCases400 ++ sqliteJsonEscapeTailCases600) do
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless expected == "error:" ++ SQLite.Text.hexBytes (SQLite.Diagnostic.bytes message) do
        fail s!"JSON escape tail error differs: {sql}: {message}"
    | .ok (_, results) =>
        let values ← (expected.splitOn "|").mapM fun field => match SQLSurface.value (.text field) with
          | .ok value => pure value | .error message => fail message
        unless results.getLast?.map (·.rows) == some [values] do
          fail s!"JSON escape tail result differs: {sql}"

def expectSQLiteJsonRemove : IO Unit := do
  for (arguments, expected) in (sqliteJsonRemoveCases0 ++ sqliteJsonRemoveCases250 ++ sqliteJsonRemoveCases500 ++ sqliteJsonRemoveCases750 ++ sqliteJsonRemoveCases1000 ++ sqliteJsonRemoveCases1250 ++ sqliteJsonRemoveCases1500 ++ sqliteJsonRemoveCases1750 ++ sqliteJsonRemoveCases2000 ++ sqliteJsonRemoveCases2250 ++ sqliteJsonRemoveCases2500 ++ sqliteJsonRemoveCases2750 ++ sqliteJsonRemoveCases3000 ++ sqliteJsonRemoveCases3250) do
    let call := "jsonb_remove(" ++ arguments ++ ")"
    let sql := "SELECT typeof(" ++ call ++ "),hex(" ++ call ++ "),hex(quote(" ++ call ++ "));"
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless expected == "error:" ++ SQLite.Text.hexBytes (SQLite.Diagnostic.bytes message) do
        fail s!"jsonb_remove error differs: {sql}: {message}"
    | .ok (_, results) =>
        let values ← (expected.splitOn "|").mapM fun field => match SQLSurface.value (.text field) with
          | .ok value => pure value | .error message => fail message
        unless results.getLast?.map (·.rows) == some [values] do
          fail s!"jsonb_remove bytes differ: {sql}"

def expectSQLiteJsonPatch : IO Unit := do
  for (arguments, expected) in (sqliteJsonPatchCases0 ++ sqliteJsonPatchCases250 ++ sqliteJsonPatchCases500 ++ sqliteJsonPatchCases750 ++ sqliteJsonPatchCases1000 ++ sqliteJsonPatchCases1250 ++ sqliteJsonPatchCases1500 ++ sqliteJsonPatchCases1750 ++ sqliteJsonPatchCases2000 ++ sqliteJsonPatchCases2250 ++ sqliteJsonPatchCases2500 ++ sqliteJsonPatchCases2750) do
    let call := "jsonb_patch(" ++ arguments ++ ")"
    let sql := "SELECT typeof(" ++ call ++ "),hex(" ++ call ++ "),hex(quote(" ++ call ++ "));"
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless expected == "error:" ++ SQLite.Text.hexBytes (SQLite.Diagnostic.bytes message) do
        fail s!"jsonb_patch error differs: {sql}: {message}"
    | .ok (_, results) =>
        let values ← (expected.splitOn "|").mapM fun field => match SQLSurface.value (.text field) with
          | .ok value => pure value | .error message => fail message
        unless results.getLast?.map (·.rows) == some [values] do
          fail s!"jsonb_patch bytes differ: {sql}"

def expectSQLiteJsonText : IO Unit := do
  for (expression, expected) in (sqliteJsonTextCases0 ++ sqliteJsonTextCases250 ++ sqliteJsonTextCases500 ++ sqliteJsonTextCases750 ++ sqliteJsonTextCases1000 ++ sqliteJsonTextCases1250 ++ sqliteJsonTextCases1500 ++ sqliteJsonTextCases1750) do
    let sql := "SELECT typeof(" ++ expression ++ "),subtype(" ++ expression ++ "),hex(" ++ expression ++ "),hex(quote(" ++ expression ++ "));"
    match CoreSQL.execute Core.State.empty sql with
    | .error message => unless expected == "error:" ++ SQLite.Text.hexBytes (SQLite.Diagnostic.bytes message) do
        fail s!"JsonText error differs: {sql}: {message}"
    | .ok (_, results) =>
        let fields := expected.splitOn "|"
        let values ← (fields.zipIdx).mapM fun (field, index) => do
          let input : Value ← if index == 1 then
              match field.toInt? with
              | some integer => pure (.integer integer)
              | none => fail "invalid oracle subtype field"
            else pure (.text field)
          match SQLSurface.value input with
          | .ok value => pure value | .error message => fail message
        unless results.getLast?.map (·.rows) == some [values] do
          fail s!"JsonText value/subtype differs: {sql}"

end SQLeanite.Tests
