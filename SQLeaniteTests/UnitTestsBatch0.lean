import SQLeaniteTests.WithoutRowidReseek
import SQLeaniteTests.WithoutRowidKeys
import SQLeaniteTests.WithoutRowid
import SQLeaniteTests.EarlyForeignInsert
import SQLeaniteTests.MultipleErrorEffects
import SQLeaniteTests.RegisterInputEffects
import SQLeaniteTests.RegisterInputPlans
import SQLeaniteTests.PartialIndexes
import SQLeaniteTests.ExpressionIndexes
import SQLeaniteTests.CollatedIndexes
import SQLeaniteTests.CompositeIndexes
import SQLeaniteTests.CompositeTableKeys
import SQLeaniteTests.ErrorEffects
import SQLeaniteTests.RaiseAbort
import SQLeaniteTests.RecursiveTriggers
import SQLeaniteTests.NestedInsert
import SQLeaniteTests.BeforeInsert
import SQLeaniteTests.BeforeUpdate
import SQLeaniteTests.ForeignCounters
import SQLeaniteTests.BeforeDelete
import SQLeaniteTests.TriggerConstraints
import SQLeaniteTests.TriggerPrograms
import SQLeaniteTests.TriggerExecution
import SQLeaniteTests.TriggerCatalog
import SQLeaniteTests.ExpectCheckAddColumn
import SQLeaniteTests.ExpectForeignKeyPragmas
import SQLeaniteTests.ExpectSQLiteJoinRangeRegressions
import SQLeaniteTests.ExpectSQLiteJoinRangeTraversal
import SQLeaniteTests.ExpectSQLiteJoinedDeclaredNullability
import SQLeaniteTests.ExpectSQLiteJoinedFixedWhere
import SQLeaniteTests.ExpectSQLiteJoinedNullFilterOrder
import SQLeaniteTests.ExpectSQLiteJoinedNullableData
import SQLeaniteTests.ExpectSQLiteJoinedReadPrefix
import SQLeaniteTests.ExpectSQLiteSingleReadPrefixControls
import SQLeaniteTests.UTF16Provenance

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def unitTestsBatch0 : Array (String × IO Unit) := #[
  ("WITHOUT ROWID BEFORE programs reseek real primary keys after deletion, reinsertion and rekeying", expectWithoutRowidReseek),
  ("WITHOUT ROWID keys retain directions, repeated collation fields and secondary locators", expectWithoutRowidKeys),
  ("WITHOUT ROWID retains actual primary records, secondary locators and private ordinal isolation", expectWithoutRowid),
  ("Composite table keys retain actual automatic origins, PK ordinals and rowid effects", expectCompositeTableKeys),
  ("Composite index records preserve every key, actual rowids and tuple uniqueness", expectCompositeIndexes),
  ("Collated index keys preserve declared predicates, metadata and actual unique victims", expectCollatedIndexes),
  ("expression indexes retain computed keys, physical rowids and unique actions", expectExpressionIndexes),
  ("Single-write FK lookup fails before the point and cannot cancel against old orphans", expectEarlyForeignInsert),
  ("Later INSERT input failures retain earlier actual point connection effects", expectMultipleErrorEffects),
  ("External SELECT register coroutines retain earlier point effects on late failures", expectRegisterInputEffects),
  ("Register input plans preserve cursor order, DISTINCT, sorter materialization and UNION yields", expectRegisterInputPlans),
  ("Partial index source, qualifying keys, metadata and transactions use actual state", expectPartialIndexes),
  ("Error outcomes preserve native connection effects while rolling back statement data", expectErrorEffects),
  ("RAISE ABORT retains dynamic messages, lazy control and unpublished failed writes", expectRaiseAbort),
  ("Recursive trigger controls retain live settings, frame depth and REPLACE register images", expectRecursiveTriggers),
  ("Nested INSERT retains lexical inputs, subtype, lazy targets and caller registers", expectNestedInsert),
  ("BEFORE INSERT freezes ordinary inputs, caches subqueries and allocates rowids after programs", expectBeforeInsert),
  ("BEFORE UPDATE freezes SET, reloads unassigned fields and preserves actual NEW register types", expectBeforeUpdate),
  ("VDBE FK counters retain signed scans, zero guards and old-orphan cancellation", expectForeignCounters),
  ("BEFORE DELETE retains original OLD and RETURNING across mutation, AFTER and rollback", expectBeforeDelete),
  ("Trigger NO ACTION checks wait for the outer statement; discarded SET and schema contexts stay exact", expectTriggerConstraints),
  ("Trigger programs preserve captured DML, SELECT inputs, inherited policy and nested preparation", expectTriggerPrograms),
  ("AFTER row triggers retain OLD/NEW images, preparation, counters and transaction semantics", expectTriggerExecution),
  ("Persistent trigger source, UPDATE OF, catalog bytes and transaction identity", expectTriggerCatalog),
  ("UTF-16 predicates retain native bytes, correlated captures and BETWEEN error order", expectUTF16Predicates),
  ("UTF-16 native TEXT survives derived sources, JOIN, min/max and concatenation", expectUTF16Provenance),
  ("UTF-16 native byte provenance and compound/window ordering", expectUTF16Edges),
  ("UTF-16 record translation, runtime encoding and BINARY comparison", expectUTF16Reads),
  ("Persistent VIEW sources, lexical isolation, ALTER and physical catalog evidence", expectPersistentViews),
  ("Derived and CTE declarations preserve scopes, collation and private state", expectDerivedCollations),
  ("Compound declared collations preserve set keys and IN operand metadata", expectDeclaredCompounds),
  ("IN query collation distinguishes explicit operators, declarations and scalar results", expectDeclaredMembership),
  ("Declared column collations preserve explicit priority and checked persistence", expectDeclaredCollations),
  ("Generated INSERT retains original target-list provenance and arity diagnostics", expectGeneratedInsertTargets),
  ("Generated ALTER preserves declaration priority and the last ordinary column", expectGeneratedColumnDDL),
  ("STORED generated programs preserve dependency order, metadata and checked persistence", expectStoredGeneratedColumns),
  ("CREATE main qualifiers preserve literal periods and certified target names", expectCreateSchemaQualification),
  ("STRICT type programs preserve ANY affinity and checked persistence", expectStrictTables),
  ("Table FOREIGN KEY programs preserve declaration order and certified child targets", expectTableForeignKeys),
  ("Foreign-key parent renames retain checked source after reopening", expectForeignKeyRename),
  ("Foreign-key inspection preserves connection state and hidden arguments", expectForeignKeyPragmas),
  ("Immediate foreign keys preserve connection flags and retained programs", expectForeignKeys),
  ("ALTER ADD COLUMN validates existing CHECK rows and retains its catalog", expectCheckAddColumn),
  ("IN table shorthand preserves certified names and compound lexical scopes", expectInTable),
  ("IN, NOT IN and EXISTS preserve set and lazy scan semantics", expectSubquerySets),
  ("JSON table traversal and subtype", expectJsonTableFunctions),
  ("Window partition ordering and ROWS frames", expectWindowFunctions),
  ("Derived INSERT inputs preserve private state and row registers", expectDerivedInsertInput),
  ("Existing zero-byte databases preserve read-only bytes and commit their first rows", expectZeroLengthDatabase),
  ("Parser subquery folding and captured-token replay", expectSubqueryFolding),
  ("UPDATE CHECK dependencies preserve rows, counters and catalog programs", expectCheckUpdateDependencies),
  ("Retained CHECK constraints and independent token replay", expectCheckConstraints),
  ("SQLite zero text-encoding cookie preserves reads", expectZeroEncoding),
  ("Automatic UNIQUE indexes and physical schema reads", expectUniqueConstraints),
  ("Retained index catalogs and checked physical images", expectIndexCatalogImage),
  ("UPSERT conflict selection and checked writes", expectUpsert),
  ("Lazy scalar queries and lexical correlation", expectScalarSubqueries),
  ("PRAGMA table functions and hidden columns", expectPragmaTableFunctions),
  ("connection last inserted rowid", expectLastInsertRowid),
  ("scoped derived and recursive queries", expectDerivedQueries),
  ("connection change counters", expectConnectionCounters),
  ("SQLite binary JSON escape and Unicode sentinel regressions", expectSQLiteJsonBinaryEscapes),
  ("SQLite byte diagnostics preserve invalid UTF-8", expectSQLiteByteDiagnostics),
  ("SQLite identical payload and indexed UPDATE publication", expectSQLiteIdenticalUpdates),
  ("SQLite JSON types, lengths and path lookup", expectSQLiteJsonAccess),
  ("SQLite JSON preparation and original function spelling", expectSQLiteJsonPreparationErrors),
  ("SQLite JSON validity flags, JSON5 and JSONB", expectSQLiteJsonValid),
  ("SQLite joined range and mixed-affinity regressions", expectSQLiteJoinRangeRegressions),
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
  ("SQLite variable page-size encoding", expectSQLiteSizedPages),
  ("SQLite index source transactions", expectSQLiteIndexSource),
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
  ("SQLite DEFERRED transactions and ignored TRANSACTION names", expectSQLiteTransactionNames),
  ("SQLite completed-statement output before errors", expectSQLiteScriptOutput),
  ("SQLite CAST type grammar, affinity and independent replay", expectSQLiteCastTypeGrammar),
  ("SQLite identifier keywords and explicit/implicit aliases", expectSQLiteIdentifierGrammar),
  ("SQLite script source preservation and committed prefixes", expectSQLiteScriptPrefix),
  ("SQLite read-only transaction publication", expectSQLiteReadTransaction),
  ("SQLite SAVEPOINT nesting, release and rollback", expectSQLiteSavepoint),
  ("SQLite AUTOINCREMENT history, ignored rows, rollback and persistence", expectSQLiteAutoIncrement),
  ("SQLite indexed primary types, NULL namespaces and exact numeric equality", expectSQLiteIndexedPrimaryTypes),
  ("SQLite column types, exact spans, empty affinity and canonical persistence", expectSQLiteColumnTypes),
  ("SQLite named column and table constraints, grammar and persistence", expectSQLiteNamedConstraints),
  ("SQLite blob prefix adjacency, aliases and independent token replay", expectSQLiteBlobAdjacency),
  ("SQLite DEFAULT values, delayed errors, old records and conflict replacement", expectSQLiteColumnDefaults),
  ("SQLite primary-key schema policies, precedence and pending rowids", expectSQLiteSchemaPrimaryConflict),
  ("SQLite schema NOT NULL conflict policies and persisted overrides", expectSQLiteSchemaNullConflict),
  ("SQLite CREATE TABLE AS SELECT metadata and Core write trace", expectSQLiteCreateTableAs),
  ("SQLite PRAGMA atom spelling and explicit schemas", expectSQLitePragmaArguments),
  ("SQLite application header PRAGMAs and transactions", expectSQLiteApplicationHeaderPragmas),
  ("SQLite application header journal and WAL persistence", expectSQLiteApplicationHeaderFiles),
  ("SQLite schema PRAGMA metadata and read immutability", expectSQLiteSchemaPragma),
  ("SQLite index catalog metadata and physical contents", expectSQLiteIndexSchema),
  ("SQLite DROP COLUMN preserves rows and shifts key/index positions", expectSQLiteSchemaDropColumn),
  ("SQLite ADD COLUMN and omitted trailing record fields", expectSQLiteSchemaAdd),
  ("SQLite empty index identifiers survive reopen and schema changes", expectSQLiteEmptyIndex),
  ("SQLite table and column renames preserve rows and index metadata", expectSQLiteSchemaRename),
  ("SQLite case-insensitive binding preserves schema spelling", expectSQLiteSchemaCase),
  ("SQLite explicit INTEGER PRIMARY KEY NOT NULL metadata survives reopen", expectSQLiteIntegerNotNullMetadata),
  ("SQLite multi-VALUES evaluates discarded inputs before constraints", expectSQLiteInsertInputEvaluation),
  ("SQLite checked single-column table PRIMARY KEY", expectSQLiteTablePrimary),
  ("SQLite nullable TEXT primary keys and persisted NOT NULL", expectSQLiteNullableTextPrimary),
  ("SQLite row-value UPDATE assignments preserve width and simultaneous RHS", expectSQLiteUpdateTuples),
  ("SQLite UPDATE RETURNING uses pending rows and accepted new values", expectSQLiteUpdateReturning),
  ("SQLite INSERT RETURNING collects accepted rows before later replacements", expectSQLiteInsertReturning),
  ("SQLite UPDATE OR REPLACE re-seeks surviving pending rows", expectSQLiteUpdateReplace),
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
  ("SQLite JSON extraction error precedence", expectSQLiteJsonExtractErrors),
  ("SQLite quoted function limit diagnostics", expectSQLiteQuotedFunctionLimits),
  ("SQLite JSON escape tail consumption", expectSQLiteJsonEscapeTail),
  ("SQLite JSON text functions and subtype", expectSQLiteJsonText),
  ("SQLite scalar subtype propagation", expectSQLiteJsonSubtype),
  ("SQLite aggregate and write subtype boundaries", expectSQLiteJsonRuntime),
  ("SQLite JSON constructors and runtime tags", expectSQLiteJsonConstruct),
  ("SQLite ordinary JSON aggregate states", expectSQLiteJsonGroup),
  ("SQLite JSON replacement bytes and runtime tags", expectSQLiteJsonReplace),
  ("SQLite JSON insertion, setting and array positions", expectSQLiteJsonInsert),
  ("SQLite CTAS catalog formatting", expectSQLiteCtasCatalog),
  ("SQLite CREATE catalog normalization", expectSQLiteCreateCatalog),
  ("SQLite CREATE source execution", expectSQLiteCreateSource),
  ("SQLite ALTER ADD catalog normalization", expectSQLiteAlterCatalog),
  ("PRAGMA schema write admission", expectSQLitePragmaSchemaWriteGuard),
  ("PRAGMA quoted schema source diagnostics", expectSQLitePragmaSchemaSource),
  ("PRAGMA listing and schema diagnostics", expectSQLitePragmaListing),
  ("Cold read chunk certification", expectColdReadChunkPlanning),
  ("SQLite date NULL and host rejection order", expectSQLiteDateNull),
  ("SQLite time difference", expectSQLiteTimeDifference),
  ("SQLite date/time functions", expectSQLiteDateTime),
  ("SQLite version functions", expectSQLiteVersionFunctions),
  ("SQLite resolver diagnostic order", expectSQLiteResolutionOrder),
  ("SQLite ALTER ADD source execution", expectSQLiteAlterSource),
  ("SQLite ALTER DROP diagnostics", expectSQLiteAlterDropErrors),
  ("SQLite ALTER column source execution", expectSQLiteColumnSource),
  ("SQLite ALTER RENAME TABLE source execution", expectSQLiteRenameTableSource),
  ("SQLite trigger EOF diagnostics", expectSQLiteTriggerEof),
  ("SQLite retained catalog source through writes", expectSQLiteRetainedCatalog),
  ("SQLite default register reuse and affinity tags", expectSQLiteJsonReplaceRuntime),
  ("SQLite JSON binary merge patch", expectSQLiteJsonPatch),
  ("SQLite JSON binary removal", expectSQLiteJsonRemove),
  ("SQLite JSON SQL-value arrow", expectSQLiteJsonArrow),
  ("SQLite JSON binary extraction", expectSQLiteJsonExtract),
  ("SQLite JSON pretty rendering", expectSQLiteJsonPretty),
  ("SQLite JSONB binary encoding", expectSQLiteJsonBinary),
  ("SQLite joined grouped error prefix", expectSQLiteJoinedGroupPrefix),
  ("SQLite joined aggregate WHERE error order", expectSQLiteJoinedAggregatePredicate),
  ("SQLite aggregate WHERE error order", expectSQLiteAggregatePredicateOrder),
  ("SQLite percentile error order and group prefixes", expectSQLitePercentileExecution),
  ("SQLite ordinary percentile aggregates", expectSQLitePercentile),
  ("SQLite JSON text and binary error positions", expectSQLiteJsonPosition),
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
  ("SQLite zero-LIMIT joins validate without value evaluation", expectSQLiteJoinZeroLimit),
  ("SQLite empty-side outer ON validates without value evaluation", expectSQLiteJoinEmptyOuterOn),
  ("SQLite static joined conditions and outer-ON error ordering", expectSQLiteJoinStaticConditions),
  ("SQLite parser-time literal NULL-test preparation", expectSQLiteLiteralNullPreparation),
  ("SQLite joined IN lists, NULL and left-operand affinity", expectSQLiteJoinInList),
  ("SQLite joined comparison collations and value-preserving wrappers", expectSQLiteJoinComparisonWrappers),
  ("SQLite joined projection wrappers and result collations", expectSQLiteJoinProjectionWrappers),
  ("SQLite RIGHT/FULL join null extension and match accounting", expectSQLiteRightFullJoins),
  ("SQLite RIGHT USING merged values, qualification and CTAS metadata", expectSQLiteRightUsing),
  ("SQLite FULL USING coalesced values, affinity, ordering and CTAS names", expectSQLiteFullUsing),
  ("SQLite joined predicate aliases and source-name priority", expectSQLiteJoinAliases),
  ("SQLite joined compound result slots and expression binding", expectSQLiteJoinCompoundBinding),
  ("SQLite joined scalar expressions, aggregates and dynamic ON", expectSQLiteJoinedExpressions),
  ("SQLite joined evaluation order and early WHERE filtering", expectSQLiteJoinEvaluationOrder),
  ("SQLite joined cursor initialization and empty-input search keys", expectSQLiteJoinCursorInitialization),
  ("SQLite reduced outer cursors and transitive rowid ranges", expectSQLiteJoinReducedCursor),
  ("SQLite joined fixed-column affinity and inner WHERE filters", expectSQLiteJoinedFixedColumns),
  ("SQLite joined null-range and singleton cursor search", expectSQLiteJoinedNullRangeSearch),
  ("SQLite joined original and commuted search constraints", expectSQLiteJoinedSearchTermOrder),
  ("SQLite joined declared nullability and singleton IN", expectSQLiteJoinedDeclaredNullability),
  ("SQLite joined fixed WHERE and null-filter cursor ordering", expectSQLiteJoinedFixedWhere),
  ("SQLite BETWEEN cursor plans and original outer markings", expectSQLiteBetweenCursorPlans),
  ("SQLite range traversal and USING sort boundaries", expectSQLiteJoinRangeTraversal),
  ("SQLite BETWEEN, CASE and conditional constants", expectSQLiteBetweenConstants),
  ("SQLite joined nullable data and dependent point searches", expectSQLiteJoinedNullableData),
  ("SQLite joined null-filter preparation and source selection", expectSQLiteJoinedNullFilterOrder),
  ("SQLite nonnull rowid filters and empty inner ranges", expectSQLiteJoinedEmptyFilters),
  ("SQLite single-source read prefix controls", expectSQLiteSingleReadPrefixControls),
  ("SQLite single-source read prefixes in both file modes", expectSQLiteSingleReadPrefixFiles),
  ("SQLite joined read prefixes survive errors in both file modes", expectSQLiteJoinedReadPrefix),
  ("SQLite computed rowid lookup traversal in streaming and sorted joins", expectSQLiteComputedJoinTraversal),
  ("SQLite first scalar argument collation includes column defaults", expectSQLiteFunctionArgumentCollations),
  ("SQLite joined NULL-safe and Boolean IS comparisons", expectSQLiteJoinIs),
  ("SQLite truth conversion in joined ON/WHERE", expectSQLiteJoinTruth),
  ("SQLite join rowid lookup traversal", expectSQLiteJoinLookupScan),
  ("SQLite declared rowid names across joined sources", expectSQLiteJoinRowidNames),
  ("SQLite visible column names and implicit rowid aliases", expectSQLiteColumnVisibility),
  ("SQLite joined literal and name atoms", expectSQLiteJoinAtoms),
  ("SQLite join NULL placement and collations", expectSQLiteJoinSort),
  ("SQLite join ORDER BY names and positions", expectSQLiteJoinOrder),
  ("SQLite join DISTINCT and LIMIT/OFFSET", expectSQLiteJoinWindow),
  ("SQLite USING/NATURAL merged columns and CTAS", expectSQLiteJoinUsing),
  ("SQLite stored-column join comparison affinity", expectSQLiteJoinAffinity),
  ("SQLite join keywords and optional ON", expectSQLiteJoinSyntax),
  ("SQLite zero-row writes preserve files and publish sequence initialization", expectSQLiteEmptyWritePublication),
  ("SQLite constant LIMIT/OFFSET expressions and independent replay", expectSQLiteLimitExpressions),
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
    #[#[.integer 0]])
]

end SQLeanite.Tests
