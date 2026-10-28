# Sourced by live-path-check.sh; shares its failure status and scratch files.

if grep -q 'overflow-chain|' scripts/run-reverse-differential.sh &&
   grep -q 'auto-vacuum|' scripts/run-reverse-differential.sh &&
   grep -q 'post-vacuum|' scripts/run-reverse-differential.sh &&
   grep -q 'freelist-after-delete|' scripts/run-reverse-differential.sh &&
   grep -q 'multipage-interior|' scripts/run-reverse-differential.sh &&
   grep -q 'wal-mode|' scripts/run-reverse-differential.sh &&
   grep -q 'real-values|' scripts/run-reverse-differential.sh &&
   grep -q 'blob-values|' scripts/run-reverse-differential.sh; then
  ok "reverse corpus covers every file feature claimed as accepted"
else
  fail "a file feature is claimed as accepted with no reverse-direction cell"
fi

if [ -f docs/COMPATIBILITY.md ] &&
   scripts/run-reverse-differential.sh --markdown > "$scratch_parity" 2>/dev/null &&
   cmp -s "$scratch_parity" docs/COMPATIBILITY.md; then
  ok "generated compatibility document is current"
else
  fail "docs/COMPATIBILITY.md is stale; regenerate with --markdown"
fi

# Every shrink/refill image must now be clean; keep both strict runners wired.
if grep -q 'regress-page-reclaim.sh' scripts/reproduce-all.sh &&
   grep -q 'run-forward-compat.sh' scripts/reproduce-all.sh &&
   grep -q 'empty image failed integrity_check' scripts/regress-page-reclaim.sh &&
   ! grep -q 'orphan_bound' scripts/regress-page-reclaim.sh &&
   ! grep -q 'excepted=' scripts/run-forward-compat.sh; then
  ok "indexed page reclamation requires clean images after every phase"
else
  fail "strict page-reclamation checks or their runners are missing"
fi

# The one assumed law is disclosed as *checkable*, and that claim rests entirely on
# `TextRoundtrips` having a `Decidable` instance. If the instance disappears, the
# assumption silently becomes irreducible and TRUST.md is overstating.
if grep -q 'instance (value : String) : Decidable (TextRoundtrips value)' \
     "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'def UTF8Roundtrips' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'per-string check at the boundary' docs/TRUST.md; then
  utf8_sites=$(rg -c '\(utf8 : (CoreDecode\.)?UTF8Roundtrips\)' -g '*.lean' \
    SQLeanite/ | awk -F: '{s+=$2} END {print s+0}')
  if grep -q "$utf8_sites hypothesis positions" docs/TRUST.md; then
    ok "the assumed UTF-8 law is decidable and its $utf8_sites sites are counted"
  else
    fail "TRUST.md's UTF-8 site count is stale: tree says $utf8_sites"
  fi
else
  fail "the assumed UTF-8 law lost its decidability or its disclosure"
fi

# `PostImageCertificate` must stay constructive. A new constructor that accepts a
# bare decoder equation would turn the crash theorem's post-image premise into an
# assumption, which is exactly what its docstring forbids.
post_image_block=$(awk '
  /^inductive PostImageCertificate/ { inside = 1 }
  inside { print }
  inside && /^$/ { inside = 0 }
' "$audit_sources/SQLeanite/CoreDurability.lean")
post_image_constructors=$(printf '%s\n' "$post_image_block" | grep -c '^  | ')
if ! grep -q 'no constructor accepting an opaque decoder equation' \
       "$audit_sources/SQLeanite/CoreDurability.lean"; then
  fail "PostImageCertificate lost the docstring stating its design rule"
elif printf '%s\n' "$post_image_block" | grep -q 'CoreDecode.decode'; then
  fail "a PostImageCertificate constructor accepts a decoder equation"
elif [ "$post_image_constructors" -ne 5 ]; then
  fail "PostImageCertificate has $post_image_constructors constructors, expected 5"
else
  ok "PostImageCertificate stays constructive across all 5 alternatives"
fi

# The write side must reach the same bag algebra the read side denotes into, and
# it must reach it through the *same* abstraction function -- two abstractions
# would make the write and read statements incomparable, which is precisely the
# gap this closes. `coreRow` is the shared one.
if grep -q 'CoreReadSemantics.coreRow' SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'KRelation.single' SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'execute_insert_denotes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'tableDenotation_orderedUpsert_fresh' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "live INSERT reaches the bag algebra through the read side's abstraction"
else
  fail "the write side has no bag denotation, or uses a second abstraction"
fi

# The round trip has to be reachable from SQL text at both ends, or it presumes a
# parser step the executable does not perform.
if grep -q 'insertText_bytes_reopen_readText_denotes' \
     SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'CoreSQL.execute state insertText' SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'CoreSQL.execute { database := reopened } readText' \
     SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'CorePageCodec.encodeBulk' SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'CoreDecode.decode image.fileBytes' \
     SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'insertText_bytes_reopen_readText_denotes' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "write text, bytes, reopen and read text compose into one audited theorem"
else
  fail "the write/read round trip is not reachable from live SQL text"
fi

# Freshness is what separates INSERT from REPLACE at the denotation level. If it
# stops being carried, the bag statement silently weakens to replace-then-union.
if grep -q 'existing.rowid.value ≠ row.rowid.value' "$audit_sources/SQLeanite/CoreEngine.lean" &&
   grep -q 'existing.rowid.value ≠ row.rowid.value' SQLeanite/CoreEndToEnd.lean &&
   grep -q 'existing.rowid.value ≠ row.rowid.value' SQLeanite/CoreWriteBytes.lean; then
  ok "INSERT carries rowid freshness from the table through to the byte level"
else
  fail "rowid freshness is checked but not carried into the postcondition"
fi

# The parity artifact is generated from the audit, so a witness that is renamed,
# deleted or dropped from `ProofAxioms.lean` makes the table stale and this fails.
# A hand-maintained parity table is exactly the kind of claim that rots quietly.
if scripts/popl-parity.sh --check > "$scratch_parity" 2>&1; then
  ok "$(cat "$scratch_parity")"
else
  cat "$scratch_parity" >&2
  fail "POPL parity table is stale or names an unaudited witness"
fi

# The bridge must be about the same projection the executor runs, not a copy of
# it: `permuted_projection_denotes` is stated over `Core.Query.projectedRows`
# through `query_eval_denotes`, which is the same route `execute_query_denotes`
# takes. If the executor's projection stops going through `Query.projectedRows`,
# this pins that the bridge has to move with it.
if grep -q 'query.columns.map row.value' "$audit_sources/SQLeanite/CoreEngine.lean" &&
   grep -q 'permutedColumns_map_value' "$audit_sources/SQLeanite/CoreReadSemantics.lean" &&
   grep -q 'Core.Query.projectedRows' "$audit_sources/SQLeanite/CoreReadSemantics.lean"; then
  ok "permutation bridge is stated over the executor's own projection"
else
  fail "permutation bridge drifted from the live Query.projectedRows"
fi

if grep -q 'execute_query_denotes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_join_denotes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_group_denotes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_count_denotes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_sum_denotes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_extreme_denotes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'compound_denotes' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "every live Core read form reaches the multiplicity denotation"
else
  fail "a live Core read form is detached from the relational semantics"
fi

if grep -q 'where_\.leftOnly = true' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   grep -q 'left\.rows\.filter (selectsLeft where_)' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   grep -q 'matchingRows_pushLeft' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'leftOuterRows_pushLeft' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "live inner and left-outer joins use proved preserved-side pushdown"
else
  fail "the live join planner detached from safe left-predicate pushdown"
fi

if grep -q 'CoreOptimizerBridge.optimizeJoin leftTable rightTable query' \
     "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'def innerJoinPlan' "$audit_sources/SQLeanite/CoreOptimizerBridge.lean" &&
   grep -q 'def leftOuterJoinPlan' "$audit_sources/SQLeanite/CoreOptimizerBridge.lean" &&
   grep -q 'symbolicLeftOnPlan' "$audit_sources/SQLeanite/CoreOptimizerBridge.lean" &&
   grep -q 'symbolicLeftWherePlan' "$audit_sources/SQLeanite/CoreOptimizerBridge.lean" &&
   grep -q 'optimize_innerJoinPlan_eval' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'optimize_leftOuterJoinPlan_eval' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'optimizeJoin_eval' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "live inner and width-aware left joins execute the denotational optimizer"
else
  fail "live joins bypass or detached from denotational refinement"
fi

if grep -q 'CoreOptimizerBridge.optimizeCompoundOp operation' \
     "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreCompound.combine operation left right' \
     "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreSQL.combineRows_denotes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'optimizeCompoundOp_eq' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "live compound SELECTs execute the SQL-key bag refinement and operator optimizer"
else
  fail "live compound SELECTs bypass or detached from denotational refinement"
fi

if ! grep -q 'CellPagination.paginateCells' "$audit_sources/SQLeanite/CoreOverflow.lean" &&
   grep -q 'RecursivePageBTree.IndexStore' "$audit_sources/SQLeanite/CoreOverflow.lean" &&
   grep -q 'provisional.retarget? resolved.cells' \
     "$audit_sources/SQLeanite/CoreOverflow.lean" &&
   grep -q 'IndexStore.retarget?_pageCount' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'IndexStore.retarget?_represents' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "index encoding retains one proof-carrying page topology"
else
  fail "index encoding re-chunks or detached from its topology proofs"
fi

if grep -q 'CoreFileAdapter.loadOpenState paths' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'CorePageLoad.openGenerated? source' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'CoreDecode.rebuildCanonicalDatabase base.tables indexEntries' \
     "$audit_sources/SQLeanite/CorePageLoad.lean" &&
   grep -q 'loadOpenTables? source tableEntries' \
     "$audit_sources/SQLeanite/CorePageLoad.lean" &&
   grep -q 'retargetOpenTables? initialStates database.tables' \
     "$audit_sources/SQLeanite/CorePageLoad.lean" &&
   grep -q 'CorePageLoad.open?_represents' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CorePageLoad.openGenerated?_represents' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreDecode.rebuildCanonicalDatabase_overflowEncoded' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "generated write opens validate tables once and restore proved index metadata"
else
  fail "the write opener detached from its proof-carrying combined loader"
fi

if grep -q 'CoreLazyFileEngine.execute? paths sql' Main.lean &&
   grep -q 'CoreFileAdapter.lookupPrimaryRowDecision paths tableName rowid' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'CoreDecode.lookupTableRowidIOFrom schema source rowid' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'CoreFile.hasGeneratedImageStamp header' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'encodeBulk_generatedHeader' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'lookupTableRowidWith source.readPage' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'lookupTableRowidWith (m := Id)' "$audit_sources/SQLeanite/CoreDecode.lean"; then
  ok "foreign primary fallback retains the reference page traversal and provenance checks"
else
  fail "the cold primary-key path detached from traversal or provenance proof"
fi

if grep -q 'CoreFileAdapter.lookupGeneratedPrimaryRowWith generated paths' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'cursor.seek target fuel' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'Runtime.Record.readRowWithSource schema source cell' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'Runtime.ReadPager.ofPath' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'let some page ← cursor.pager.get pageNumber' \
     SQLeanite/Runtime/TableCursor.lean &&
   grep -q 'CoreDecode.decodeRowCellIOFrom schema source' \
     SQLeanite/Runtime/Record.lean; then
  ok "generated reads use pager/cursor/record layers (runtime boundary, not a refinement proof)"
else
  fail "generated read layers detached from the shipped path"
fi

if grep -q 'let index := view.lowerBound target' SQLeanite/Runtime/TableCursor.lean &&
   grep -q 'pageNumber (some cache.tableViews)' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'let some view := TablePage.decode? page' SQLeanite/Runtime/TableCursor.lean &&
   grep -q 'if ordered : CheckedOrder.adjacent' SQLeanite/Runtime/TablePage.lean &&
   grep -q 'LowerBound.search' SQLeanite/Runtime/TablePage.lean &&
   grep -q 'encodedSize record = cell.payloadSize.val' SQLeanite/Runtime/Record.lean &&
   grep -q '(source.pageCount + 1) cell.input' SQLeanite/Runtime/Record.lean &&
   grep -q '^#print axioms SQLeanite.Runtime.TablePage.View.lowerBound_eq_linear' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q '^#print axioms SQLeanite.Runtime.TablePage.View.lowerBound_present' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q '^#print axioms SQLeanite.Runtime.Record.decodeRowCell_eq_reference' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q '^#print axioms SQLeanite.Runtime.Record.readRowWithSource_eq_reference' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "checked binary search and allocation-free size validation use audited refinements"
else
  fail "SQLite-style page/record algorithms detached from their checked premises or proofs"
fi

if grep -q 'lookupGeneratedPrimaryRange' SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'CoreDecode.lookupTableRangeIOFrom schema source' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'tableRangeCandidatesWith source.readPage' \
     "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'tableRangeCandidatesWith (m := Id)' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'lookupTableRangeFrom_encodeChunkNodeWithOverflow_exact' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "cold primary ranges use exact separator-directed traversal"
else
  fail "the cold primary-range path detached from its shared proved traversal"
fi

if grep -q 'lookupGeneratedIndexCandidates' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'PageReadCache.create' SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'query (some cache)' SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'preadPageSourceCached paths.main count cache' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'executeReadStatements? paths statementList' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'Core.Index.isImplicitPrimary schema' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'CanonicalIndexSQL.parseGeneratedCertified' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'CoreFile.hasGeneratedImageStamp header' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'lookupIndexValueIOFrom source value' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'lookupIndexRangeIOFrom source operation value' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'lookupTableRowidIOFrom schema source' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'lookupIndexValueFrom_encodeIndex_exact' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'lookupIndexValueFrom_text_encodeIndex_exact' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'lookupIndexRangeFrom_encodeIndex_exact' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'implicitPrimaryIndexes_areImplicit' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "cold read batches cache raw pages and use exact generated-index traversal"
else
  fail "the cold generated-index path detached from provenance or exactness"
fi

if grep -q 'lookupGeneratedOrderedPrefix paths' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'lookupIndexPrefixIOFrom source limit' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'indexPrefixWith source.readPage' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'indexPrefixWith (m := Id) source.readPage' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'indexPrefixFrom_text_encodeIndex_exact' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "cold ORDER BY LIMIT uses a proved multi-leaf index cursor"
else
  fail "the cold ORDER BY prefix detached from its shared exact traversal"
fi

if grep -q 'lookupGeneratedPrimaryJoin paths' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'CoreDecode.decodeSubtreeRowsIOFrom rightSchema source' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'CoreDecode.lookupTableRangeIOFrom leftSchema' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'evalPrimaryKeyCandidates' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'evalPrimaryKeyCandidates_eq_eval' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'lookupTableRangeFrom_encodeChunkNodeWithOverflow_exact' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "cold primary-key joins use a complete bounded-left merge"
else
  fail "the cold primary-key join detached from range or semantic exactness"
fi

if grep -q 'table.rows.mergeSort (integerIndexRowLe index)' \
     "$audit_sources/SQLeanite/CoreFile.lean" &&
   grep -q 'table.rows.mergeSort (textIndexRowLe index)' \
     "$audit_sources/SQLeanite/CoreFile.lean" &&
   grep -q 'CoreFile.sortedIndexRows table index' \
     "$audit_sources/SQLeanite/CoreOverflow.lean" &&
   grep -q 'integerIndexRowLe_trans' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'textIndexRowLe_trans' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'expectedIndexEntries_eq_sortSource' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "physical INTEGER/TEXT indexes use proved merge-sort paths"
else
  fail "physical index encoding detached from its proved fast ordering"
fi

if grep -q 'preparePageDirectedIndexDelete? validated' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'deleteIndexEntriesBatch?' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'let (cell, rest) ← takeExact cellLength input' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'let certified ← certifyDecodedIndexAt? entry.rootPage' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'localizedIndexReadable_of_onStorage' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'deletedRowsOrdered?_length' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreFileAdapter.takeExact_spec' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'certifyDecodedIndex?_exact' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "indexed bulk DELETE carries an exact decoded post-state certificate"
else
  fail "page-directed indexed DELETE detached from its physical certificate"
fi

if grep -q 'let source := byteArrayPageSource input count' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   ! sed -n '/def loadOpenState/,/structure CertifiedIndexEncoding/p' \
      "$audit_sources/SQLeanite/CoreFileAdapter.lean" | grep -q 'CoreDecode.pages'; then
  ok "validated write-open reads pages directly from the file buffer"
else
  fail "validated write-open regressed to whole-file list pagination"
fi

if grep -q 'preparePageDirectedIndexInsert? validated' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'insertIndexEntryNoSplit?' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'let certified ← certifyDecodedIndexAt? entry.rootPage' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'localizedIndexReadable_of_onStorage' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'firstInserted_mem_after' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'certifyDecodedIndex?_exact' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "single-row indexed INSERT carries an exact decoded post-state certificate"
else
  fail "page-directed indexed INSERT detached from its physical certificate"
fi

# 6. The binary must really produce a SQLite file the C implementation accepts.
if [ -x .lake/build/bin/sqleanite ] && [ -x "$sqlite_bin" ]; then
  tmp=$(mktemp -d)
  printf 'CREATE TABLE t(id INTEGER PRIMARY KEY, v);\nINSERT INTO t VALUES(1,%s);\n' "'x'" > "$tmp/s.sql"
  .lake/build/bin/sqleanite --verified-file "$tmp/db" "$tmp/s.sql" >/dev/null 2>&1 || fail "sqleanite could not write a database"
  if [ "$("$sqlite_bin" "$tmp/db" 'PRAGMA integrity_check;' 2>&1)" = "ok" ]; then
    ok "C sqlite3 accepts a Lean-written file"
  else
    fail "C sqlite3 rejected a Lean-written file"
  fi
  {
    printf 'CREATE TABLE d(id INTEGER PRIMARY KEY, v);\n'
    printf 'CREATE INDEX d_v ON d(v);\nBEGIN;\n'
    i=1
    while [ "$i" -le 60 ]; do
      printf "INSERT INTO d VALUES(%s,'v-%s');\n" "$i" "$((i % 7))"
      i=$((i + 1))
    done
    printf 'COMMIT;\n'
  } > "$tmp/delete-seed.sql"
  .lake/build/bin/sqleanite --verified-file "$tmp/delete-db" \
    "$tmp/delete-seed.sql" >/dev/null 2>&1 ||
      fail "sqleanite could not seed an indexed DELETE database"
  printf 'DELETE FROM d WHERE id > 40;\n' > "$tmp/delete.sql"
  .lake/build/bin/sqleanite --verified-file "$tmp/delete-db" \
    "$tmp/delete.sql" >/dev/null 2>&1 ||
      fail "page-directed indexed DELETE failed"
  delete_check=$("$sqlite_bin" -batch -noheader "$tmp/delete-db" \
    'PRAGMA integrity_check; SELECT count(*) FROM d; SELECT count(*) FROM d INDEXED BY d_v;' 2>&1)
  if [ "$delete_check" = "ok
40
40" ]; then
    ok "page-directed indexed DELETE is integrity-check clean"
  else
    fail "C sqlite3 rejected the page-directed indexed DELETE"
  fi
  printf "INSERT INTO d VALUES(100,'v-1');\n" > "$tmp/insert.sql"
  .lake/build/bin/sqleanite --verified-file "$tmp/delete-db" \
    "$tmp/insert.sql" >/dev/null 2>&1 ||
      fail "page-directed indexed INSERT failed"
  insert_check=$("$sqlite_bin" -batch -noheader "$tmp/delete-db" \
    "PRAGMA integrity_check; SELECT count(*) FROM d; SELECT count(*) FROM d INDEXED BY d_v WHERE v='v-1';" 2>&1)
  if [ "$insert_check" = "ok
41
7" ]; then
    ok "page-directed indexed INSERT is integrity-check clean"
  else
    fail "C sqlite3 rejected the page-directed indexed INSERT"
  fi
  printf 'INSERT INTO t VALUES(2,%s);\n' "'y'" > "$tmp/write.sql"
  chmod 444 "$tmp/db"
  if .lake/build/bin/sqleanite --verified-file "$tmp/db" "$tmp/write.sql" \
      >"$tmp/readonly.out" 2>"$tmp/readonly.err"; then
    fail "sqleanite wrote a read-only database"
  elif grep -q '^Error: attempt to write a readonly database$' \
      "$tmp/readonly.err" &&
      ! grep -q 'uncaught exception' "$tmp/readonly.err"; then
    ok "read-only writes produce an ordinary SQLite-style diagnostic"
  else
    fail "read-only write diagnostic was misleading"
  fi
  chmod 644 "$tmp/db"
  # Unix SQLite treats one-byte files as empty; two bytes are corrupt.
  printf xx > "$tmp/bad"
  if .lake/build/bin/sqleanite --verified-file "$tmp/bad" </dev/null \
      >"$tmp/bad.out" 2>"$tmp/bad.err"; then
    fail "sqleanite accepted a corrupt database"
  elif grep -q '^Error: file is not a database$' "$tmp/bad.err" &&
      ! grep -q 'uncaught exception' "$tmp/bad.err"; then
    ok "corrupt input rejection is a normal diagnostic, not a crash"
  else
    fail "corrupt input rejection still looks like an uncaught crash"
  fi
  rm -r -- "$tmp"
else
  printf 'skip - binary or configured SQLite reference unavailable\n'
fi


if python3 scripts/check_module_boundaries.py --reaches SQLeanite.CoreSQL SQLeanite.CoreNullConflict &&
   grep -q 'schemaInsertRows state tableName stored.schema' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'executeSchemaUpdate state tableName' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreNullConflict.prepare stored.schema values old.isSome' SQLeanite/CoreDefaultConflict.lean &&
   grep -q 'notNullConflict == column.notNullConflict' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'notNullConflictChars column.notNullConflict' "$audit_sources/SQLeanite/CanonicalSchemaSQL.lean" &&
   grep -q 'Core.Column.restoreNotNullConflict' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - schema NOT NULL policies reach checked writes and invertible persistence'
else
  echo 'FAIL - schema NOT NULL policy wiring is incomplete'
  exit 1
fi
